/*
 *   Project: Speedith
 * 
 * File name: CliOptions.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2010 Matej Urbas
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

import java.util.logging.Level;
import java.util.logging.Logger;
import org.apache.commons.cli.AlreadySelectedException;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import speedith.Main;
import static speedith.i18n.Translations.i18n;

/**
 * Parses and manages command line interface arguments for Speedith.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class CliOptions {

    // <editor-fold defaultstate="collapsed" desc="Private Constants">
    /**
     * The usage description string (displayed in command line help).
     */
    private static final String USAGE_SYNTAX = "java -jar Speedith.jar";
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Disabled Constructor">
    private CliOptions() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Command Line Arguments">
    /**
     * Returns the command line argument definitions for Speedith.
     * @return the command line argument definitions for Speedith.
     */
    public static Options getCliOptions() {
        Options opts = new Options();

        ///
        /// Batch mode options
        ///
        // ---- Batch mode flag
        OptionGroup batchMode = new OptionGroup();
        Option batchFlag = new Option("b", "batch", false, i18n("CLI_ARG_DESCRIPTION_BATCH"));
        batchMode.addOption(batchFlag);
        try {
            batchMode.setSelected(batchFlag);
        } catch (AlreadySelectedException ex) {
            Logger.getLogger(Main.class.getName()).log(Level.SEVERE, null, ex);
        }
        ///
        /// END: Batch mode options
        ///
        opts.addOptionGroup(batchMode);

        // ---- Help option
        Option helpFlag = new Option("?", "help", false, i18n("CLI_ARG_DESCRIPTION_HELP"));
        opts.addOption(helpFlag);

        // ---- Spider diagram formula
        Option spiderDiagram = new Option("sd", "spider-diagram", true,
                i18n("CLI_ARG_DESCRIPTION_SD"));
        spiderDiagram.setArgName(i18n("CLI_ARG_SD_VALUE_NAME"));
        opts.addOption(spiderDiagram);

        return opts;
    }

    /**
     * Prints the command line arguments description and usage help for
     * Speedith.The string
     */
    public static void printCliHelp() {
        printCliHelp(null);
    }

    /**
     * Prints the command line arguments description and usage help.
     * @param opts the <a href="http://commons.apache.org/cli/">Jakarta CLI</a>
     * options to use for constructing the help. If {@code opts} is {@code null}
     * then this method calls {@link CliOptions#getCliOptions() } to get the options
     * and prints those.
     */
    public static void printCliHelp(Options opts) {
        HelpFormatter help = new HelpFormatter();
        help.printHelp(USAGE_SYNTAX, opts == null ? getCliOptions() : opts, true);
    }
    // </editor-fold>
}
