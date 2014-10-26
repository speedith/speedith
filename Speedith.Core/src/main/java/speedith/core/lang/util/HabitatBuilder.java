package speedith.core.lang.util;

import speedith.core.lang.Region;
import speedith.core.lang.Zone;

import java.util.*;

public class HabitatBuilder {
  private final Map<String, Region> spiderHabitats;

  public HabitatBuilder(HashMap<String, Region> spiderHabitats) {
    this.spiderHabitats = spiderHabitats;
  }

  public HabitatBuilder(SortedMap<String, Region> spiderHabitats) {
    this.spiderHabitats = spiderHabitats;
  }

  public HabitatBuilder() {
    this(new HashMap<String, Region>());
  }

  public Map<String, Region> get() {
    return Collections.unmodifiableMap(spiderHabitats);
  }

  public HabitatBuilder addHabitat(String spider, Region habitat) {
    HashMap<String, Region> spiderHabitats = new HashMap<>(get());
    spiderHabitats.put(spider, habitat);
    return new HabitatBuilder(spiderHabitats);
  }

  public HabitatBuilder addHabitat(String spider, List<Zone> habitat) {
    return addHabitat(spider, new Region(habitat));
  }

  public HabitatBuilder addHabitat(String spider, RegionBuilder habitat) {
    return addHabitat(spider, habitat.get());
  }

  public HabitatBuilder addHabitats(HabitatBuilder otherSpiderHabitats) {
    HashMap<String, Region> spiderHabitats = new HashMap<>(get());
    spiderHabitats.putAll(otherSpiderHabitats.get());
    return new HabitatBuilder(spiderHabitats);
  }

  public RegionBuilder region(String spider) {
    return new RegionBuilder(get().get(spider));
  }

  public static HabitatBuilder habitat(String spider, RegionBuilder habitat) {
    return emptyHabitat().addHabitat(spider, habitat);
  }

  public static HabitatBuilder emptyHabitat() {return new HabitatBuilder();}
}
