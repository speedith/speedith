package speedith.core.reasoning.automatic;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface AutomaticProverProvider {

    AutomaticProver getAutomaticProver();

    String getAutomaticProverName();

    String getDescription();

    String getPrettyName();
}
