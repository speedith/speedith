package speedith.core.lang.test;

import speedith.core.lang.util.RegionBuilder;
import speedith.core.lang.util.RegionUtils;

import static speedith.core.reasoning.util.unitary.TestSpiderDiagrams.POWER_REGION_ABC;

public class RegionsABC {
  public static final RegionBuilder FULL_ABC_REGION = RegionUtils.builder(POWER_REGION_ABC);
  public static final RegionBuilder REGION_ABC = FULL_ABC_REGION.within("A", "B", "C");
  public static final RegionBuilder REGION_AC_B = FULL_ABC_REGION.within("A", "C").outside("B");
  public static final RegionBuilder REGION_AB_C = FULL_ABC_REGION.within("A", "B").outside("C");
  public static final RegionBuilder REGION_BC_A = FULL_ABC_REGION.within("B", "C").outside("A");
  public static final RegionBuilder REGION_A_BC = FULL_ABC_REGION.within("A").outside("B", "C");
  public static final RegionBuilder REGION_B_AC = FULL_ABC_REGION.within("B").outside("A", "C");
  public static final RegionBuilder REGION_C_AB = FULL_ABC_REGION.within("C").outside("A", "B");
}
