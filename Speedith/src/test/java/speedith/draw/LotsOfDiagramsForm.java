package speedith.draw;

import speedith.ui.SpiderDiagramPanel;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public class LotsOfDiagramsForm extends javax.swing.JFrame {
    private final DiagramTestPortfolio diagramTestPortfolio = new DiagramTestPortfolio();
    private SpiderDiagramPanel spiderDiagramPanel;
    private int spiderDiagramIndex = -1;

    public LotsOfDiagramsForm() {
        setLayout(new BorderLayout());

        spiderDiagramPanel = new SpiderDiagramPanel();
        add(spiderDiagramPanel, BorderLayout.CENTER);

        initButtonUp();

        initButtonDown();

        setDefaultCloseOperation(DISPOSE_ON_CLOSE);

        showNextDiagram();

        setExtendedState(MAXIMIZED_BOTH);
    }

    public static void main(String[] args) {
        new LotsOfDiagramsForm().setVisible(true);
    }

    private void initButtonDown() {
        JButton buttonDown = new JButton("Show another diagram");
        add(buttonDown, BorderLayout.WEST);
        buttonDown.addActionListener(new AbstractAction() {
            @Override
            public void actionPerformed(ActionEvent e) {
                showPreviousDiagram();
            }
        });
    }

    private void initButtonUp() {
        JButton buttonUp = new JButton("Show another diagram");
        add(buttonUp, BorderLayout.EAST);
        buttonUp.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                showNextDiagram();
            }
        });
    }

    private void showPreviousDiagram() {
        spiderDiagramIndex = (spiderDiagramIndex < 1 ? diagramTestPortfolio.size() : spiderDiagramIndex) - 1;
        showDiagram();
    }

    private void showNextDiagram() {
        spiderDiagramIndex = (spiderDiagramIndex + 1) % diagramTestPortfolio.size();
        showDiagram();
    }

    private void showDiagram() {
        spiderDiagramPanel.setDiagram(diagramTestPortfolio.getDiagramAt(spiderDiagramIndex));
    }
}
