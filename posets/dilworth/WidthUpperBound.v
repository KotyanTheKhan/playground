(* WidthUpperBound — facade.
   The proof is split across the upper_bound/ subdirectory; see
   docs/superpowers/specs/2026-05-01-widthupperbound-refactor-design.md
   for the file map. External clients that previously imported
   WidthUpperBound continue to work unchanged. *)

From Dilworth Require Export
  upper_bound.Slices
  upper_bound.HallDefect
  upper_bound.BaseCases
  upper_bound.Iter
  upper_bound.HallKernel
  upper_bound.Cover
  upper_bound.Merge
  upper_bound.Backward.
