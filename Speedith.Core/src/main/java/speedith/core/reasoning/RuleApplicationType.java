package speedith.core.reasoning;

import java.awt.*;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public enum RuleApplicationType {

    INTERACTIVE("Interactive", Color.ORANGE),
    AUTOMATIC("Automatic",new Color(0xAA88FF)),
    TACTIC("Tactic",new Color(0xEE5555));

    private String name;

    private Color color;

    RuleApplicationType(String name, Color color) {
        this.name = name;
        this.color = color;
    }

    public String getName() {
        return name;
    }

    public Color getColor() {
        return color;
    }
}
