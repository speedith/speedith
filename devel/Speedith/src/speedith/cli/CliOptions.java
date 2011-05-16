/*
 *   Project: Speedith
 * 
 * File name: CliOptions.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2011 Matej Urbas
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package speedith.cli;

import java.io.OutputStream;
import java.io.PrintWriter;
import org.apache.commons.cli.AlreadySelectedException;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.GnuParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import static speedith.i18n.Translations.i18n;

/**
 * Parses and manages command line interface arguments for Speedith.
 * <p>To actually parse the command lines arguments, call
 * {@link CliOptions#parse(java.lang.String[])}.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class CliOptions extends Options {
    public static final String OPTION_HELP = "?";

    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The usage description string (displayed in command line help).
     */
    private static final String USAGE_SYNTAX = "java -jar Speedith.jar";
    /**
     * The name of the 'spider-diagram' command line argument.
     * <p>With this argument the user has to specify the actual 'spider-diagram'
     * expression. For a syntax of this expression, see the
     * {@link speedith.core.lang.reader.SpiderDiagramsReader} class (in the
     * <span style="font-style:italic;">Speedith.Core</span> project) for more
     * information.</p>
     */
    public static final String OPTION_SD = "sd";
    /**
     * This option tells Speedith to run in batch mode (without a user
     * interface).
     */
    public static final String OPTION_BATCH_MODE = "b";
    // </editor-fold>
    //<editor-fold defaultstate="collapsed" desc="Private Fields">
    /**
     * Contains the parsed command line arguments.
     */
    private CommandLine parsedArguments;
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new instance of Speedith's command line options parser.
     * <p>To actually parse the command lines arguments, call
     * {@link CliOptions#parse(java.lang.String[])}.</p>
     */
    public CliOptions() {
        initialise();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Help printing">
    /**
     * Prints the command line arguments description and usage help for
     * Speedith.
     */
    public void printHelp() {
        HelpFormatter help = new HelpFormatter();
        help.printHelp(USAGE_SYNTAX, this, true);
    }

    /**
     * Prints the command line arguments description and usage help for
     * Speedith to the given output.
     * @param out the output to write the help to.
     */
    public void printHelp(PrintWriter out) {
        if (out == null) {
            throw new IllegalArgumentException("The argument 'out' must not be null.");
        }
        HelpFormatter help = new HelpFormatter();
        help.printHelp(out, 80, USAGE_SYNTAX, i18n("CLI_HELP_HEADER"), this, 10, 5, null, true);
    }

    /**
     * Prints the command line arguments description and usage help for
     * Speedith to the given output.
     * @param out the output to write the help to.
     */
    public void printHelp(OutputStream out) {
        if (out == null) {
            throw new IllegalArgumentException("The argument 'out' must not be null.");
        }
        final PrintWriter writer = new PrintWriter(out);
        printHelp(writer);
        writer.flush();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Parsing">
    /**
     * Parses the given command line arguments and stores the extracted options.
     * <p>These options are available through the {@code get} methods of this
     * class (e.g.: TODO).</p>
     * @param args the command line arguments as passed to Speedith.
     * @throws ParseException this exception is thrown if the arguments could
     * not have been parsed (this is mainly due to ill-formatted input).
     */
    public void parse(String args[]) throws ParseException {
        CommandLineParser parser = new GnuParser();
        parsedArguments = parser.parse(this, args);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Options">
    /**
     * Returns the spider diagram expression provided by the user through
     * command line arguments (through the {@link CliOptions#OPTION_SD sd option}.
     * @return a string with the syntax as described (see the
     * {@link speedith.core.lang.reader.SpiderDiagramsReader} class for more
     * information).
     */
    public String getSpiderDiagram() {
        areOptionsParsed();
        return parsedArguments.getOptionValue(OPTION_SD);
    }
    
    /**
     * Indicates whether the user provided the 'batch mode' option in the
     * command line arguments.
     * <p>This flag tells Speedith whether to run without the graphical user
     * interface.</p>
     * @return a flag telling whether the user provided the 'batch mode' option
     * in the command line arguments.
     */
    public boolean isBatchMode() {
        areOptionsParsed();
        return parsedArguments.hasOption(OPTION_BATCH_MODE);
    }
    
    /**
     * Indicates whether the user provided the 'help' option in the command line
     * arguments.
     * <p>This flag tells Speedith whether to print the usage help text.</p>
     * @return a flag that tells whether to print the usage help text.
     */
    public boolean isHelp() {
        areOptionsParsed();
        return parsedArguments.hasOption(OPTION_HELP);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Initialisation">
    private void initialise() throws RuntimeException, IllegalArgumentException {
        ///
        /// ---- Batch mode options
        ///
        // ---- Batch mode flag
        OptionGroup batchMode = new OptionGroup();
        Option batchFlag = new Option(OPTION_BATCH_MODE, "batch", false, i18n("CLI_ARG_DESCRIPTION_BATCH"));
        batchMode.addOption(batchFlag);
        try {
            batchMode.setSelected(batchFlag);
        } catch (AlreadySelectedException ex) {
            throw new RuntimeException(i18n("ERR_CLI_SETUP_FAILED"), ex);
        }
        ///
        /// END: ---- Batch mode options
        ///
        addOptionGroup(batchMode);

        // ---- Help option
        Option helpFlag = new Option(OPTION_HELP, "help", false, i18n("CLI_ARG_DESCRIPTION_HELP"));
        addOption(helpFlag);

        // ---- Spider diagram formula
        Option spiderDiagram = new Option(OPTION_SD, "spider-diagram", true, i18n("CLI_ARG_DESCRIPTION_SD"));
        spiderDiagram.setArgName(i18n("CLI_ARG_SD_VALUE_NAME"));
        addOption(spiderDiagram);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Methods">
    /**
     * Checks if the command line options have been parsed and are available for
     * querying.
     * <p>This method throws an exception iff the {@link CliOptions#parsedArguments}
     * field is {@code null}.</p>
     * @throws RuntimeException thrown iff the {@link CliOptions#parsedArguments}
     * field is {@code null}.
     */
    private void areOptionsParsed() throws RuntimeException {
        if (parsedArguments == null) {
            throw new RuntimeException(i18n("ERR_CLI_ARGS_NOT_PARSED_YET"));
        }
    }
    // </editor-fold>
}
