package speedith.draw;

import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.lang.Zone;
import speedith.core.lang.Zones;
import speedith.ui.SpiderDiagramPanel;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static speedith.core.lang.Zones.*;
import static speedith.core.reasoning.rules.transformers.CopyContoursTransformerTest.*;

public class LotsOfDiagramsForm extends javax.swing.JFrame {
    private SpiderDiagramPanel spiderDiagramPanel;
    private int spiderDiagramIndex = -1;
    private List<? extends SpiderDiagram> spiderDiagrams = new ArrayList<>(Arrays.asList(
            SpiderDiagrams.createPrimarySD(null, null, Arrays.asList(zoneBMinusA, zoneBAndA), Arrays.asList(zoneBAndA, zoneAMinusB)),
            SpiderDiagrams.createPrimarySD(null, null, sameRegionWithNewContours(extendRegionWithNewContour(Arrays.asList(Zone.fromInContours("A")), "B"), "C"), allZonesForContours("A", "B", "C")),
            SpiderDiagrams.createPrimarySD(null, null, sameRegionWithNewContours(Arrays.asList(Zone.fromInContours("B")), "A", "C"), allZonesForContours("A", "B", "C")),
            SpiderDiagrams.createPrimarySD(null, null, sameRegionWithNewContours(Arrays.asList(Zone.fromInContours("B")), "A"), sameRegionWithNewContours(Arrays.asList(Zone.fromInContours("B")), "A")),
            SpiderDiagrams.createPrimarySD(null, null, getZonesOutsideContours(allZonesForContours("A", "B", "C", "D"), "C", "B"), Zones.allZonesForContours("A", "B", "C", "D")),
            SpiderDiagramPanelTest.getSDExample1(),
            SpiderDiagramPanelTest.getSDExample2(),
            SpiderDiagramPanelTest.getSDExample3()
    ));

    public LotsOfDiagramsForm() {
        setLayout(new BorderLayout());
        spiderDiagramPanel = new SpiderDiagramPanel();
        add(spiderDiagramPanel, BorderLayout.CENTER);
        JButton button1 = new JButton("Show another diagram");
        add(button1, BorderLayout.NORTH);

        button1.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                showNextDiagram();
            }
        });

        showNextDiagram();

        setDefaultCloseOperation(DISPOSE_ON_CLOSE);

        pack();
    }

    public static void main(String[] args) {
        new LotsOfDiagramsForm().setVisible(true);
    }

    private void showNextDiagram() {
        spiderDiagramIndex = (spiderDiagramIndex + 1) % spiderDiagrams.size();
        spiderDiagramPanel.setDiagram(spiderDiagrams.get(spiderDiagramIndex));
        pack();
    }
}
