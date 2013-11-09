package speedith.core.reasoning.util.unitary;

import speedith.core.lang.*;

import java.util.*;

public class TestSpiderDiagrams {
    public static final ArrayList<Zone> vennABCZones = Zones.allZonesForContours("A", "B", "C");
    public static final PrimarySpiderDiagram diagramSpeedithPaperD1 = getDiagramSpeedithPaperD1();

    public static PrimarySpiderDiagram getDiagramD1PrimeFromSpeedithPaper() {
        SortedSet<Zone> initialPresentZones = diagramSpeedithPaperD1.getPresentZones();
        ArrayList<Zone> presentZones = Zones.sameRegionWithNewContours(initialPresentZones, "E");
        presentZones.removeAll(Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(presentZones, "A"), "E"));
        presentZones.remove(Zone.fromInContours("A", "C").withOutContours("B", "D", "E"));

        ArrayList<Zone> vennABCDEZones = Zones.allZonesForContours("A", "B", "C", "D", "E");
        TreeSet<Zone> shadedZones = new TreeSet<>();
        shadedZones.addAll(Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(vennABCDEZones, "E"), "C"));
        shadedZones.addAll(Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(vennABCDEZones, "A"), "E"));
        shadedZones.addAll(Zones.getZonesInsideAllContours(vennABCDEZones, "A", "B"));
        shadedZones.addAll(Zones.getZonesInsideAllContours(vennABCDEZones, "B", "C"));
        shadedZones.addAll(Zones.getZonesInsideAllContours(vennABCDEZones, "C", "D"));

        TreeSet<Zone> spider2Region = new TreeSet<>();
        spider2Region.addAll(Zones.getZonesInsideAllContours(presentZones, "B"));
        spider2Region.add(Zone.fromOutContours("A", "B", "C", "D", "E"));
        spider2Region.add(Zone.fromOutContours("A", "B", "C", "E").withInContours("D"));

        Map<String, Region> habitats = new TreeMap<>();
        habitats.put("s1", new Region(Zones.getZonesInsideAllContours(presentZones, "C")));
        habitats.put("s2", new Region(spider2Region));

        return SpiderDiagrams.createPrimarySD(habitats.keySet(), habitats, shadedZones, presentZones);
    }

    public static PrimarySpiderDiagram getDiagramSpeedithPaperD2() {
        return getDiagramSpeedithPaperD2("A", "E");
    }

    public static PrimarySpiderDiagram getDiagramSpeedithPaperD2(String outsideContour, String insideContour) {
        String contourC = "C";
        String contourF = "F";
        ArrayList<Zone> abcdPowerRegion = Zones.allZonesForContours(outsideContour, contourF, contourC, insideContour);
        ArrayList<Zone> shaded_E_A = Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(abcdPowerRegion, outsideContour), insideContour);
        ArrayList<Zone> shaded_C = Zones.getZonesInsideAllContours(abcdPowerRegion, contourC);
        ArrayList<Zone> shaded_F_ACE = Zones.getZonesInsideAnyContour(Zones.getZonesInsideAllContours(abcdPowerRegion, contourF), outsideContour, contourC, insideContour);

        TreeSet<Zone> presentZones = new TreeSet<>(abcdPowerRegion);
        presentZones.removeAll(shaded_E_A);
        presentZones.removeAll(shaded_C);
        presentZones.removeAll(shaded_F_ACE);

        TreeSet<Zone> shadedZones = new TreeSet<>();
        shadedZones.addAll(shaded_E_A);
        shadedZones.addAll(shaded_C);
        shadedZones.addAll(shaded_F_ACE);

        TreeMap<String, Region> habitats = new TreeMap<>();
        habitats.put("s1", new Region(Zone.fromInContours(outsideContour, insideContour, contourC).withOutContours(contourF)));
        habitats.put("s2", new Region(
                Zone.fromInContours(contourF).withOutContours(outsideContour, contourC, insideContour),
                Zone.fromOutContours(outsideContour, contourC, insideContour, contourF)
        ));
        habitats.put("s3", new Region(
                Zone.fromInContours(contourF).withOutContours(outsideContour, contourC, insideContour),
                Zone.fromOutContours(outsideContour, contourC, insideContour, contourF)
        ));

        return SpiderDiagrams.createPrimarySD(habitats.keySet(), habitats, shadedZones, presentZones);
    }

    public static PrimarySpiderDiagram getDiagramSpeedithPaperD1() {
        ArrayList<Zone> abcdPowerRegion = Zones.allZonesForContours("A", "B", "C", "D");
        ArrayList<Zone> shaded_C_A = Zones.getZonesInsideAllContours(Zones.getZonesOutsideContours(abcdPowerRegion, "A"), "C");
        ArrayList<Zone> shaded_CBD = Zones.getZonesInsideAnyContour(Zones.getZonesInsideAnyContour(abcdPowerRegion, "B", "D"), "C");
        ArrayList<Zone> shaded_AB = Zones.getZonesInsideAllContours(abcdPowerRegion, "A", "B");

        TreeSet<Zone> presentZones = new TreeSet<>(abcdPowerRegion);
        presentZones.removeAll(shaded_C_A);
        presentZones.removeAll(shaded_CBD);
        presentZones.removeAll(shaded_AB);
        presentZones.removeAll(shaded_AB);

        TreeSet<Zone> shadedZones = new TreeSet<>(shaded_C_A);
        shadedZones.addAll(shaded_CBD);
        shadedZones.addAll(shaded_AB);

        TreeMap<String, Region> habitats = new TreeMap<>();
        habitats.put("s1", new Region(Zone.fromInContours("A", "C").withOutContours("B", "D")));
        habitats.put("s2", new Region(
                Zone.fromInContours("B", "D").withOutContours("A", "C"),
                Zone.fromInContours("D").withOutContours("B", "A", "C"),
                Zone.fromInContours("B").withOutContours("D", "A", "C"),
                Zone.fromOutContours("B", "D", "A", "C")
        ));

        return SpiderDiagrams.createPrimarySD(habitats.keySet(), habitats, shadedZones, presentZones);
    }

    public static PrimarySpiderDiagram getDiagramABCWhereCContainsA() {
        ArrayList<Zone> zonesInsideAC_outsideC = Zones.getZonesOutsideContours(Zones.getZonesInsideAnyContour(vennABCZones, "A", "C"), "C");

        TreeSet<Zone> presentZones = new TreeSet<>(vennABCZones);
        presentZones.removeAll(zonesInsideAC_outsideC);

        return SpiderDiagrams.createPrimarySD(null, null, zonesInsideAC_outsideC, presentZones);
    }

    public static PrimarySpiderDiagram getVenn2Diagram(String contour1, String contour2) {
        return SpiderDiagrams.createPrimarySD(null, null, null, Zones.allZonesForContours(contour1, contour2));
    }

    public static PrimarySpiderDiagram getVenn3Diagram(String contour1, String contour2, String contour3) {
        return SpiderDiagrams.createPrimarySD(null, null, null, Zones.allZonesForContours(contour1, contour2, contour3));
    }
}