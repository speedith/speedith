package speedith.core.lang.util;

import speedith.core.lang.Region;
import speedith.core.lang.Zone;
import speedith.core.lang.Zones;

import java.util.Collection;
import java.util.Collections;
import java.util.SortedSet;

public class RegionBuilder {
  private final Region region;

  public RegionBuilder(Region region) {
    this.region = region;
  }

  public RegionBuilder(Collection<Zone> initialRegion) {
    this(new Region(initialRegion));
  }

  public Region get() {
    return region;
  }

  public static RegionBuilder emptyRegion() {
    return new RegionBuilder(Collections.<Zone>emptyList());
  }

  public RegionBuilder within(String... contours) {
    return new RegionBuilder(Zones.getZonesInsideAllContours(region.sortedZones(), contours));
  }

  public RegionBuilder outside(String... contours) {
    return new RegionBuilder(Zones.getZonesOutsideContours(region.sortedZones(), contours));
  }

  public RegionBuilder union(RegionBuilder region) {
    return new RegionBuilder(this.region.union(region.get()));
  }

  public SortedSet<Zone> asZones() {
    return region.sortedZones();
  }
}
