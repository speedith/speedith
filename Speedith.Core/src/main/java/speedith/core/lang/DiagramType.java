package speedith.core.lang;

/**
 * The types of diagrams the different rules and provers within Speedith can be applied to.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public enum DiagramType {

    SpiderDiagram("spider_diagram", "Spider Diagrams"),
    EulerDiagram("euler_diagram", "Euler Diagrams");


    private final String preferenceKey;

    private final String prettyName;

    DiagramType(String preference_name, String prettyName) {
        this.preferenceKey = preference_name;
        this.prettyName = prettyName;
    }

    public String getPreferenceKey() {
        return preferenceKey;
    }

    public String getPrettyName() {
        return prettyName;
    }


    @Override
    public String toString() {
        return prettyName;
    }
}
