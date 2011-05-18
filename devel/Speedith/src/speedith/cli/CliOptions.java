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
import speedith.core.lang.export.SDExporting;
import static speedith.i18n.Translations.i18n;

/**
 * Parses and manages command line interface arguments for Speedith.
 * <p>To actually parse the command lines arguments, call
 * {@link CliOptions#parse(java.lang.String[])}.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class CliOptions extends Options {

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
    /**
     * This option tells Speedith to print out the 'usage help', with a list of
     * all command line options with their descriptions.
     */
    public static final String OPTION_HELP = "?";
    /**
     * The output (export) format to use when printing spider diagrams (e.g.: to
     * the standard output).
     * <p>The list of all available export formats can be obtained with the
     * '{@link CliOptions#OPTION_LOF list output formats}' option.</p>
     */
    public static final String OPTION_OF = "of";
    /**
     * This option makes Speedith to print a list of all available spider
     * diagram formula export formats.
     */
    public static final String OPTION_LOF = "lof";
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
        return getParsedOptions().getOptionValue(OPTION_SD);
    }
    
    /**
     * Returns the spider diagram formula output format that should be used
     * when exporting spider diagrams (to the standard output) in the batch
     * mode.
     * @return the output format name (see {@link SDExporting} for more
     * information).
     */
    public String getOutputFormat() {
        return getParsedOptions().getOptionValue(OPTION_OF);
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
        return getParsedOptions().hasOption(OPTION_BATCH_MODE);
    }
    
    /**
     * Indicates whether the user provided the 'help' option in the command line
     * arguments.
     * <p>This flag tells Speedith whether to print the usage help text.</p>
     * @return a flag that tells whether to print the usage help text.
     */
    public boolean isHelp() {
        return getParsedOptions().hasOption(OPTION_HELP);
    }
    
    /**
     * Indicates whether the user provided the 'list output formats' option in
     * the command line arguments.
     * <p>This flag tells Speedith whether to print the list of all known spider
     * diagram formula export formats.</p>
     * @return a flag that tells whether to print the list of all known spider
     * diagram formula export formats.
     */
    public boolean isListOutputFormats() {
        return getParsedOptions().hasOption(OPTION_LOF);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Initialisation">
    private void initialise() throws RuntimeException, IllegalArgumentException {
        ///
        /// ---- Batch mode options
        ///
        // ---- Batch mode flag
        OptionGroup batchMode = new OptionGroup();
        Option opt = new Option(OPTION_BATCH_MODE, "batch", false, i18n("CLI_ARG_DESCRIPTION_BATCH"));
        batchMode.addOption(opt);
        try {
            batchMode.setSelected(opt);
        } catch (AlreadySelectedException ex) {
            throw new RuntimeException(i18n("ERR_CLI_SETUP_FAILED"), ex);
        }
        ///
        /// END: ---- Batch mode options
        ///
        addOptionGroup(batchMode);

        // ---- Help option
        opt = new Option(OPTION_HELP, "help", false, i18n("CLI_ARG_DESCRIPTION_HELP"));
        addOption(opt);

        // ---- Spider diagram formula
        opt = new Option(OPTION_SD, "spider-diagram", true, i18n("CLI_ARG_DESCRIPTION_SD"));
        opt.setArgName(i18n("CLI_ARG_SD_VALUE_NAME"));
        addOption(opt);

        // ---- Output formula format
        opt = new Option(OPTION_OF, "output-format", true, i18n("CLI_ARG_DESCRIPTION_OF"));
        opt.setArgName(i18n("CLI_ARG_OF_VALUE_NAME"));
        addOption(opt);

        // ---- List known export formats
        opt = new Option(OPTION_LOF, "lst-output-formats", false, i18n("CLI_ARG_DESCRIPTION_LOF"));
        addOption(opt);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Private Methods">
    /**
     * Returns a non-{@code null} reference to parsed options (as read from the
     * command line arguments).
     * <p>This method throws an exception iff the {@link CliOptions#parsedArguments}
     * field is {@code null}.</p>
     * @throws RuntimeException thrown iff the {@link CliOptions#parsedArguments}
     * field is {@code null}.
     * @return a non-{@code null} reference to parsed options (as read from the
     * command line arguments).
     */
    private CommandLine getParsedOptions() throws RuntimeException {
        if (parsedArguments == null) {
            throw new RuntimeException(i18n("ERR_CLI_ARGS_NOT_PARSED_YET"));
        }
        return parsedArguments;
    }
    // </editor-fold>
}
