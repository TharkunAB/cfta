/-- Retain each source output at its own enumeration cache and native endpoint. -/
structure Output (width : Nat) (Typing : Type) where
  /-- A stop rule returns metadata. Exhausted candidate selection returns none. -/
  metadata : Option (Metadata Typing)
  /-- The enumeration cache belongs to this output branch. -/
  cache : Cached
  /-- The caller is the native endpoint when this output is emitted. -/
  caller : Caller width
  /-- The saved queries belong to the same endpoint. -/
  queries : Queries
