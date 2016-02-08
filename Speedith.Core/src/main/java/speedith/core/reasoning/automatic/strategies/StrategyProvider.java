package speedith.core.reasoning.automatic.strategies;

/**
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public interface StrategyProvider {

    Strategy getStrategy();

    String getStrategyName();

    String getDescription();

    String getPrettyName();
}
