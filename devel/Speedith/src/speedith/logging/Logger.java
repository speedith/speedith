/*
 *   Project: Speedith
 * 
 * File name: Logger.java
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
package speedith.logging;

import java.util.logging.Level;
import java.util.logging.FileHandler;
import speedith.Main;
import static speedith.i18n.Translations.*;

/**
 * The main class for application-wide logging of errors, information and
 * debugging messages.
 * <p>The Speedith's main logger writes its messages to special log files. Their
 * path and name is given by {@link Logger#LogFilePath}. The number of log files
 * through which this logger rotates is specified in {@link
 * Logger#LogFileCount}. The maximum size of each log file is given by {@link 
 * Logger#MaxLogFileSize}.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class Logger {
    
    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The path pattern of Speedith's log files.
     * <p>For a description of the format of this string, see {@link java.util.logging.Logger}.</p>
     */
    public static final String LogFilePath = "%h/.Speedith.log.%g";
    /**
     * The maximum number of logging files (through which this logger will
     * rotate).
     */
    public static final int LogFileCount = 5;
    /**
     * The maximum size of the logging files in bytes.
     */
    public static final int MaxLogFileSize = 1 << 20;
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * This method behaves exactly the same as the standard {@link
     * java.util.logging.Logger#log(java.util.logging.Level, java.lang.String, java.lang.Throwable)
     * logging method} of the {@link java.util.logging.Logger Logger} class.
     * @param level
     * @param msg
     * @param ex
     */
    public static void log(Level level, String msg, Throwable ex) {
        LoggerInstanceHolder.ApplicationLogger.log(level, msg, ex);
    }
    
    /**
     * Returns the application-wide logger that is used throughout Speedith.
     * @return the application-wide logger that is used throughout Speedith.
     */
    public static java.util.logging.Logger getLogger() {
        return LoggerInstanceHolder.ApplicationLogger;
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="Singleton Holder Class: LoggerInstanceHolder">
    /**
     * This helper class is used for thread-safe and lazy instantiation of the
     * logging infrastructure.
     */
    private static final class LoggerInstanceHolder {
        /**
         * This field holds the application-wide logger (a singleton). All
         * logging in Speedith should be performed through this guy.
         */
        public static final java.util.logging.Logger ApplicationLogger;
        
        static {
            ApplicationLogger = java.util.logging.Logger.getLogger(Main.class.getName());
            try {
                FileHandler fh = new FileHandler(LogFilePath, MaxLogFileSize, LogFileCount, false);
                fh.setLevel(Level.ALL);
                ApplicationLogger.setUseParentHandlers(false);
                ApplicationLogger.addHandler(fh);
            } catch (Exception ex) {
                throw new RuntimeException(i18n("ERR_LOGGING_SETUP_FAILED"), ex);
            }
        }
    }
    // </editor-fold>
}
