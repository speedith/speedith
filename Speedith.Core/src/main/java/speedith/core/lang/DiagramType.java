package speedith.core.lang;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public enum DiagramType {




    SpiderDiagram("spider_diagram"),
    EulerDiagram("euler_diagram");

    private final String preferenceKey;

    DiagramType(String preference_name) {
        this.preferenceKey = preference_name;
    }

    public String getPreferenceKey() {
        return preferenceKey;
    }
}
