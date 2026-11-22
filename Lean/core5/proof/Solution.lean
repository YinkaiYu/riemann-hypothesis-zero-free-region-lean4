import ComparatorChallenges.RHCore5Defs
import Core5.M19FunctorialResolution

/- The resolution rule and its functoriality are those constructed in
   Levent Alpöge's resolution library. The five fields below transfer each
   blow-up sequence to the geometry interface supplied by the competition. -/
namespace AlpogeRHCore5

theorem functorialResolutionCharZero : FunctorialResolution.FunctorialResolutionCharZero.{0} := by
  obtain ⟨R, hr, hs, hf⟩ :=
    FunctorialResolution.EmbeddedResolution.strongResolutionOfSingularitiesCharZero.{0}
  exact ⟨fun k _ _ X f _ _ _ =>
    ⟨(R k X f).length, (R k X f).tower, (R k X f).isoZero,
      (R k X f).center, (R k X f).isBlowup⟩, hr, hs, hf⟩

end AlpogeRHCore5
