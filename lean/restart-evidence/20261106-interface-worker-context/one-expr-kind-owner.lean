import Lean
import MicroCFTA.InternedFreshProbeKeys

open Lean Elab Command

private def registryKind483 (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "AXIOM"
  | .defnInfo _ => "DEFINITION"
  | .thmInfo _ => "THEOREM"
  | .opaqueInfo _ => "OPAQUE"
  | .quotInfo _ => "QUOT"
  | .inductInfo _ => "INDUCTIVE"
  | .ctorInfo _ => "CONSTRUCTOR"
  | .recInfo _ => "RECURSOR"

elab "#oneExprRegistry483" : command => do
  let env <- getEnv
  let targets : List Name :=
    [`Lean.Expr]
  let mut rows : Array Json := #[]
  for target in targets do
    let row :=
      match env.find? target with
      | none =>
        Json.mkObj [("target", Json.str target.toString),
          ("status", Json.str "ABSENT_METADATA_ONLY"),
          ("binding", Json.str "ABSENT"), ("kind", Json.null),
          ("owner", Json.null)]
      | some info =>
        let owner? : Option Name :=
          match env.getModuleIdxFor? target with
          | none => none
          | some moduleIdx => env.header.moduleNames[moduleIdx]?
        let (owner, status) :=
          match owner? with
          | none => (Json.null, "BOUND_OWNER_UNKNOWN")
          | some name => (Json.str name.toString, "BOUND_KIND_OWNER_METADATA_ONLY")
        Json.mkObj [("target", Json.str target.toString),
          ("status", Json.str status), ("binding", Json.str "BOUND"),
          ("kind", Json.str (registryKind483 info)), ("owner", owner)]
    rows := rows.push row
  liftIO <| IO.println (Json.mkObj [("scope", Json.str "ONE_LITERAL_EXPR_KIND_OWNER_METADATA_ONLY"),
    ("records", Json.arr rows)]).compress

#oneExprRegistry483
