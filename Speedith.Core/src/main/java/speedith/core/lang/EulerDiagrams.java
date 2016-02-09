package speedith.core.lang;

import java.util.Collection;

/**
 * @author Sven Linker
 * Created by sl542 on 10/11/15.
 */
public class EulerDiagrams {

    public static PrimarySpiderDiagram createPrimaryEulerDiagram(Collection<Zone> shadedZones, Collection<Zone> presentZones){
        return SpiderDiagrams.createPrimarySD(null, null, shadedZones, presentZones);
    }
}
