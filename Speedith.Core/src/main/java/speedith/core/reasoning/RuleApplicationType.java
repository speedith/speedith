package speedith.core.reasoning;

import java.awt.*;

/**
 * Distinguishes the way a rule was applied.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public enum RuleApplicationType {

    INTERACTIVE("Interactive", new Color(0xEE5555)),
    AUTOMATIC("Automatic",new Color(0x9999FF)),
    TACTIC("InferenceTactic", new Color(0x55AA55));

    private final String name;

    private final Color color;

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
