package speedith.cli;


import org.apache.commons.cli.Options;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class AnalyserOptions extends Options {

    public static final String OUTPUT_SHORT = "o";
    public static final String OUTPUT_LONG = "output";
    public static final String RECURSIVE_SHORT = "R";
    public static final String RECURSIVE_LONG = "recursive";
    public static final String INPUT_LONG = "input";
    public static final String INPUT_SHORT = "i";

    private static final long serialVersionUID = 5121836302517618707L;


    public AnalyserOptions() {
        initialise();
    }

    private void initialise() {

        addOption(RECURSIVE_SHORT,RECURSIVE_LONG, false, "traverse the given directory recursively (optional)");
        addOption(OUTPUT_SHORT, OUTPUT_LONG, true, "the output file");
        addOption(INPUT_SHORT, INPUT_LONG, true, "the input directory");
    }


}
