/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderArg.java
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
package speedith.core.reasoning.args;

/**
 * Contains the name of the contour that should be passed to an inference rule.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ContourArg extends SubDiagramIndexArg {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private final String contour;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructor">
    /**
     * Initialises an argument object for a spider-diagrammatic inference rule.
     *
     * @param subgoalIndex the index of the subgoal to target by the rule.
     * @param primarySDIndex the index of the sub-diagram to target by the rule.
     * @param contour the name of the contour that should be passed to an
     * inference rule. This parameter must not be
     * {@code null} or empty, otherwise an exception will be thrown.
     */
    public ContourArg(int subgoalIndex, int primarySDIndex, String contour) {
        super(subgoalIndex, primarySDIndex);
        if (contour == null || contour.isEmpty()) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_EMPTY_ARGUMENT", "contour"));
        }
        this.contour = contour;
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * The name of the contour that should be passed to an inference rule.
     * <p>This property is guaranteed to return a non-null and non-empty
     * string.</p>
     *
     * @return name of the spider that should be passed to an inference rule.
     */
    public String getSpider() {
        return contour;
    }
    // </editor-fold>
}
