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

import speedith.core.lang.Zone;

/**
 * This argument contains a zone.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ZoneArg extends SubDiagramIndexArg {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private final Zone zone;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Constructor">
    /**
     * Initialises an argument object for a spider-diagrammatic inference rule.
     * 
     * @param subgoalIndex the index of the subgoal to target by the rule.
     * @param primarySDIndex the index of the sub-diagram to target by the rule.
     * @param zone the zone that should be passed to the inference rule.
     */
    public ZoneArg(int subgoalIndex, int primarySDIndex, Zone zone) {
        super(subgoalIndex, primarySDIndex);
        if (zone == null) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "zone"));
        }
        this.zone = zone;
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Properties">
    /**
     * The zone that should be passed to the inference rule.
     *  <p>This property is guaranteed to return a non-null value.</p>
     * @return zone that should be passed to the inference rule.
     */
    public Zone getZone() {
        return zone;
    }
    // </editor-fold>
}
