/*
 *   Project: Speedith.Core
 * 
 * File name: Translations.java
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

package speedith.core.i18n;

/**
 * This class provides translated strings for Speedith Core library.
 * <p>To use internationalised strings in Speedith Core, import the
 * {@link speedith.core.i18n.Translations#i18n(String) i18n} method like this:</p>
 * {@code import static speedith.core.i18n.Translations.i18n; }
 * <p>and use it anywhere in your code, like this:</p>
 * {@code i18n("STRING_RESOURCE_KEY"); }
 * <p>Additional strings can be added to the {@code "speedith/core/i18n/strings"}
 * bundle (see {@link speedith.core.i18n.Translations#I18N_STRINGS_BUNDLE}).</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class Translations {

    // <editor-fold defaultstate="collapsed" desc="Disabled Constructor">
    private Translations() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constants">
    /**
     * The path to the bundle which contains translations for Speedith core.
     */
    public static final String I18N_STRINGS_BUNDLE = "speedith/core/i18n/strings";
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Translated Strings">
    /**
     * Returns a string in the language of the current locale.
     * <p>It looks up the internationalised string based on the provided
     * key.</p>
     * @param key the key of the string which to fetch.
     * @return a string in the language of the current locale.
     */
    public static String i18n(String key) {
        return java.util.ResourceBundle.getBundle(I18N_STRINGS_BUNDLE).getString(key);
    }
    // </editor-fold>
}