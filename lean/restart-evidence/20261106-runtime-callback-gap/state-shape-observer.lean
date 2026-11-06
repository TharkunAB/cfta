import Lean
import MicroCFTA.InternedFreshProbeKeys

open Lean Elab Command
universe u

private def count501 {a : Type u} : List a → Nat
  | [] => 0
  | _ :: xs => count501 xs + 1

private def nominal501 (n : Name) : Json :=
  let s := n.toString
  if s == "MicroCFTA.InternedConstructorTemplates.State" ||
      s == "MicroCFTA.InternedConstructorTemplates.State.mk" then
    Json.str s
  else Json.str "OTHER_NOMINAL_NAME_OPAQUE"

private def atom501 (e : Expr) : Json :=
  match e with
  | .bvar i => Json.mkObj [("tag", Json.str "BVAR"), ("index", toJson i)]
  | .const n us => Json.mkObj [("tag", Json.str "CONST"),
      ("known_public_nominal_text", nominal501 n),
      ("universe_argument_count", toJson (count501 us)),
      ("universe_values", Json.str "OPAQUE")]
  | .sort _ => Json.str "SORT_LEVEL_OPAQUE"
  | .fvar _ => Json.str "FVAR_PAYLOAD_OPAQUE"
  | .mvar _ => Json.str "MVAR_PAYLOAD_OPAQUE"
  | .app _ _ => Json.str "APP_CHILDREN_OPAQUE"
  | .lam _ _ _ _ => Json.str "LAMBDA_CHILDREN_OPAQUE"
  | .forallE _ _ _ _ => Json.str "FORALL_CHILDREN_OPAQUE"
  | .letE _ _ _ _ _ => Json.str "LET_CHILDREN_OPAQUE"
  | .lit _ => Json.str "LITERAL_PAYLOAD_OPAQUE"
  | .mdata _ _ => Json.str "METADATA_CHILDREN_OPAQUE"
  | .proj _ _ _ => Json.str "PROJECTION_CHILDREN_OPAQUE"

private def app501 : Nat → Expr → Json
  | 0, _ => Json.str "APP_BUDGET_EXHAUSTED"
  | fuel + 1, .app f a => Json.mkObj [("tag", Json.str "APP"),
      ("right_argument_atom", atom501 a), ("function_spine", app501 fuel f)]
  | _ + 1, e => atom501 e

private def telescope501 : Nat → Expr → Json
  | 0, _ => Json.str "BINDER_BUDGET_EXHAUSTED"
  | fuel + 1, .forallE _ domain body _ =>
      Json.mkObj [("tag", Json.str "FORALL"),
        ("domain_spine", app501 16 domain),
        ("binder_annotation", Json.str "OPAQUE"),
        ("body", telescope501 fuel body)]
  | _ + 1, e => app501 16 e

private def expectedKind501 (target : Name) (info : ConstantInfo) : Bool :=
  if target.toString == "MicroCFTA.InternedConstructorTemplates.State" then
    match info with | .inductInfo _ => true | _ => false
  else
    match info with | .ctorInfo _ => true | _ => false

elab "#stateShape501" : command => do
  let env <- getEnv
  let targets : List Name := [`MicroCFTA.InternedConstructorTemplates.State,
    `MicroCFTA.InternedConstructorTemplates.State.mk]
  let mut records : Array Json := #[]
  for target in targets do
    let row :=
      match env.find? target with
      | none => Json.mkObj [("target", Json.str target.toString),
          ("status", Json.str "STOP_ABSENT")]
      | some info =>
        if !expectedKind501 target info then
          Json.mkObj [("target", Json.str target.toString),
            ("status", Json.str "STOP_KIND")]
        else
          Json.mkObj [("target", Json.str target.toString),
            ("status", Json.str "SHAPE_METADATA_ONLY"),
            ("universe_parameter_count", toJson (count501 info.levelParams)),
            ("shape", telescope501 16 info.type),
            ("binder_names_and_Level_values", Json.str "OPAQUE"),
            ("universe_parameter_association", Json.str "UNKNOWN"),
            ("constructor_parent_parameter_identity", Json.str "UNKNOWN"),
            ("owner_and_SourceObject", Json.str "NOT_INFERRED")]
    records := records.push row
  liftIO <| IO.println (Json.mkObj [("scope", Json.str "TWO_FIXED_STATE_SHAPES_ONLY"),
    ("records", Json.arr records), ("full_State_gate", Json.str "NOT_CLOSED")]).compress

#stateShape501
