package speedith.core.lang.util;

import speedith.core.lang.Zone;

import java.util.Collection;

public class RegionUtils {
  public static RegionBuilder builder(Collection<Zone> initialRegion) {
    return new RegionBuilder(initialRegion);
  }

}
