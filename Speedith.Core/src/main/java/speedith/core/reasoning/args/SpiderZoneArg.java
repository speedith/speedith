/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderRegionArg.java
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

import java.io.Serializable;

/**
 * This inference rule argument provides the following (in addition to data
 * provided by {@link SpiderArg}): <ul> <li>a zone of the {@link
 *          SpiderRegionArg#getSpider() spider's} habitat.</li> </ul> <p>This argument
 * type is used to target a particular zone of the spider's habitat.</p>
 * <p><span style="font-weight:bold">Note</span>: there is no way for this
 * object to check whether the given zone actually is a zone contained by the
 * given spider's habitat. The object has no knowledge of the spider's
 * habitat.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SpiderZoneArg extends SpiderArg implements Serializable {

    private static final long serialVersionUID = 96187206156965663L;
    // <editor-fold defaultstate="collapsed" desc="Fields">
    private final Zone zone;
    // </editor-fold>

    /**
     * Initialises an argument object for a spider-diagrammatic inference rule.
     *
     * @param subgoalIndex the index of the subgoal to target by the rule.
     * @param primarySDIndex the index of the sub-diagram to target by the rule.
     * @param spider the name of the spider. This parameter must not be
     * {@code null} or empty, otherwise an exception will be thrown.
     * @param zone the zone of the {@link SpiderArg#getSpider()}. This parameter
     * must not be
     * {@code null}, otherwise an exception will be thrown.
     */
    public SpiderZoneArg(int subgoalIndex, int primarySDIndex, String spider, Zone zone) {
        super(subgoalIndex, primarySDIndex, spider);
        if (zone == null) {
            throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "zone"));
        }
        this.zone = zone;
    }

    /**
     * The zone of the {@link SpiderArg#getSpider()}. <p>This property is
     * guaranteed to return a non-null value.</p>
     *
     * @return the zone of the {@link SpiderArg#getSpider()}.
     */
    public Zone getZone() {
        return zone;
    }
}
