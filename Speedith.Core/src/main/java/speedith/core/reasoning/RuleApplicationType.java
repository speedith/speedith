package speedith.core.reasoning;

import java.awt.*;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public enum RuleApplicationType {

    INTERACTIVE("Interactive", new Color(0xEE5555)),
    AUTOMATIC("Automatic",new Color(0x9999FF)),
    TACTIC("Tactic", new Color(0x55AA55));

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
