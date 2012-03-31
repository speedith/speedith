/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderHabitat.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
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
package speedith.core.lang;

/**
 * Represents a contour of a spider diagram. Contains the name (label) of the
 * contour.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Contour implements SpiderDiagramElement {

    // <editor-fold defaultstate="collapsed" desc="Private Fields">
    private final String contour;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new contour information class.
     *
     * @param contour the name of the contour. This argument must not be {@code null}.
     */
    public Contour(String contour) {
        if (contour == null || contour.isEmpty()) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_EMPTY_ARGUMENT", "contour"));
        }
        this.contour = contour;
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * Returns the name of the contour.
     *
     * @return the name of the contour.
     */
    public String getContour() {
        return contour;
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Overrides">
    @Override
    public String toString() {
        return contour;
    }
    // </editor-fold>
}
