import PlutusCore.UPLC.TextEncoding

namespace UplcOptimizer

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.TextEncoding (programFromString)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Crypto.BLS12_381.G1 (bls12_381_G1_compress)
open PlutusCore.Crypto.BLS12_381.G2 (bls12_381_G2_compress)

private def byteStringText (bytes : ByteString) : String :=
  reprStr bytes

private def listText (values : List String) : String :=
  "[" ++ String.intercalate ", " values ++ "]"

private def pairText (left right : String) : String :=
  "(" ++ left ++ ", " ++ right ++ ")"

private partial def dataText : Data → String
  | .Constr tag fields => s!"Constr {tag} {listText (fields.map dataText)}"
  | .Map entries => s!"Map {listText (entries.map fun (key, value) =>
      pairText (dataText key) (dataText value))}"
  | .List elements => s!"List {listText (elements.map dataText)}"
  | .I value => s!"I {value}"
  | .B value => s!"B {byteStringText value}"

private def dataLiteralText (value : Data) : String :=
  "(" ++ dataText value ++ ")"

private def stringText (value : String) : String :=
  let escaped := value.toList.map fun c =>
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\t' => "\\t"
    | '\r' => "\\r"
    | _ =>
      if c.toNat < 32 then "\\^".push (Char.ofNat (c.toNat + 64))
      else if c.toNat == 127 then "\\DEL"
      else String.singleton c
  "\"" ++ String.join escaped ++ "\""

private def valueText (value : PlutusCore.Value.Value) : String :=
  listText (value.map fun (currency, tokens) =>
    pairText (byteStringText currency) (listText (tokens.map fun (token, amount) =>
      pairText (byteStringText token) (toString amount))))

-- Generic empty collections lose their element type in the UPLC AST. A sibling
-- in the same homogeneous collection can supply it, but a top-level empty
-- generic collection cannot be serialized without guessing.
private inductive LiteralType where
  | unknown
  | atom (name : String)
  | list (element : LiteralType)
  | array (element : LiteralType)
  | pair (left right : LiteralType)
deriving Inhabited

private def mergeType : LiteralType → LiteralType → Except String LiteralType
  | .unknown, right => .ok right
  | left, .unknown => .ok left
  | .atom left, .atom right =>
      if left == right then .ok (.atom left)
      else .error "UPLC constant collection must have a single element type"
  | .list left, .list right => .list <$> mergeType left right
  | .array left, .array right => .array <$> mergeType left right
  | .pair left₁ left₂, .pair right₁ right₂ =>
      return .pair (← mergeType left₁ right₁) (← mergeType left₂ right₂)
  | _, _ => .error "UPLC constant collection must have a single element type"

private def literalTypeText : LiteralType → Except String String
  | .unknown => .error "cannot recover the element type of an empty UPLC list or array constant"
  | .atom name => .ok name
  | .list element => return s!"(list {← literalTypeText element})"
  | .array element => return s!"(array {← literalTypeText element})"
  | .pair left right => return s!"(pair {← literalTypeText left} {← literalTypeText right})"

private structure Literal where
  type : LiteralType
  payload : String
deriving Inhabited

private def dataType : LiteralType := .atom "data"

private def collectionLiteral (collectionType : LiteralType → LiteralType)
    (elements : List Literal) : Except String Literal := do
  let elementType ← elements.foldlM (fun current literal => mergeType current literal.type) .unknown
  return ⟨collectionType elementType, listText (elements.map (·.payload))⟩

private partial def constantLiteral : Const → Except String Literal
  | .Integer value => .ok ⟨.atom "integer", toString value⟩
  | .ByteString value => .ok ⟨.atom "bytestring", byteStringText value⟩
  | .String value => .ok ⟨.atom "string", stringText value⟩
  | .Unit => .ok ⟨.atom "unit", "()"⟩
  | .Bool value => .ok ⟨.atom "bool", if value then "True" else "False"⟩
  | .Data value => .ok ⟨dataType, dataLiteralText value⟩
  | .Value value => .ok ⟨.atom "value", valueText value⟩
  | .ConstList values => do collectionLiteral .list (← values.mapM constantLiteral)
  | .ConstArray values => do collectionLiteral .array (← values.mapM constantLiteral)
  | .ConstDataList values => .ok ⟨.list dataType, listText (values.map dataLiteralText)⟩
  | .ConstPairDataList pairs => .ok ⟨.list (.pair dataType dataType),
      listText (pairs.map fun (left, right) => pairText (dataLiteralText left) (dataLiteralText right))⟩
  | .Pair (left, right) => do
      let left ← constantLiteral left
      let right ← constantLiteral right
      return ⟨.pair left.type right.type, pairText left.payload right.payload⟩
  | .PairData (left, right) =>
      .ok ⟨.pair dataType dataType, pairText (dataLiteralText left) (dataLiteralText right)⟩
  | .Bls12_381_G1_element value =>
      .ok ⟨.atom "bls12_381_G1_element", "0x" ++ (byteStringText (bls12_381_G1_compress value)).drop 1⟩
  | .Bls12_381_G2_element value =>
      .ok ⟨.atom "bls12_381_G2_element", "0x" ++ (byteStringText (bls12_381_G2_compress value)).drop 1⟩
  | .Bls12_381_MlResult _ => .error "UPLC text has no syntax for a BLS Miller-loop result constant"

private def builtinText (builtin : BuiltinFun) : Except String String := do
  let constructor := ((reprStr builtin).splitOn ".").getLast!
  let name := if builtin == .SerializeData then "serialiseData" else constructor.decapitalize
  if PlutusCore.UPLC.TextEncoding.Internal.builtinFunOfName? name == some builtin then
    return name
  else
    throw s!"unrecognized textual name for UPLC builtin {constructor}"

private partial def termText (depth : Nat) : Term → Except String String
  | .Var index =>
      if index < depth then .ok s!"x{depth - index - 1}"
      else .error s!"unbound de Bruijn index {index} at depth {depth}"
  | .Const constant => do
      let literal ← constantLiteral constant
      return s!"(con {← literalTypeText literal.type} {literal.payload})"
  | .Builtin builtin => return s!"(builtin {← builtinText builtin})"
  | .Lam body => return s!"(lam x{depth} {← termText (depth + 1) body})"
  | .Apply fn argument => return s!"[{← termText depth fn} {← termText depth argument}]"
  | .Delay value => return s!"(delay {← termText depth value})"
  | .Force value => return s!"(force {← termText depth value})"
  | .Constr tag fields => do
      let fields ← fields.mapM (termText depth)
      return "(" ++ String.intercalate " " ("constr" :: toString tag :: fields) ++ ")"
  | .Case scrutinee branches => do
      let scrutinee ← termText depth scrutinee
      let branches ← branches.mapM (termText depth)
      return "(" ++ String.intercalate " " ("case" :: scrutinee :: branches) ++ ")"
  | .Error => .ok "(error)"

/-- Emit canonical textual UPLC only when the parser recovers the same program. -/
def emitProgram : Program → Except String String
  | .Program (.Version major minor patch) term => do
      let text := s!"(program {major}.{minor}.{patch} {← termText 0 term})"
      let .Program (.Version parsedMajor parsedMinor parsedPatch) parsedTerm ←
        (programFromString text).mapError ("cannot render UPLC program: " ++ ·)
      if parsedMajor == major && parsedMinor == minor && parsedPatch == patch && parsedTerm == term then
        return text
      else
        throw "UPLC program changes when rendered as text"

end UplcOptimizer
