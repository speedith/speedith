/*
 *   Project: Speedith.Core
 * 
 * File name: AddFeet.java
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
package speedith.core.reasoning.rules;

import java.util.Locale;
import speedith.core.lang.SpiderDiagrams;
import speedith.core.lang.Operator;
import java.util.ArrayList;
import speedith.core.lang.Region;
import speedith.core.lang.PrimarySpiderDiagram;
import speedith.core.lang.CompoundSpiderDiagram;
import java.util.LinkedList;
import speedith.core.lang.IdTransformer;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.BasicInferenceRule;
import speedith.core.reasoning.Goals;
import speedith.core.reasoning.RuleApplicationException;
import speedith.core.reasoning.RuleApplicationResult;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import static speedith.core.i18n.Translations.*;

/**
 * The implementation of the 'add feet' inference rule.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class AddFeet extends SimpleInferenceRule<SpiderRegionArg> implements BasicInferenceRule {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The name of this inference rule.
     * <p>This value is returned by the {@link AddFeet#getInferenceRuleName()}
     * method.</p>
     */
    public static final String InferenceRuleName = "add_feet";
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        SpiderRegionArg arg = getTypedRuleArgs(args);
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(new AddFeetTransformer(arg), false);
        return new RuleApplicationResult(Goals.createGoalsFrom(newSubgoals));
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="InferenceRuleProvider Implementation">
    public AddFeet getInferenceRule() {
        return this;
    }

    public String getInferenceRuleName() {
        return InferenceRuleName;
    }

    public String getDescription(Locale locale) {
        return i18n(locale, "SPLIT_SPIDERS_DESCRIPTION");
    }

    public Class<SpiderRegionArg> getArgumentType() {
        return SpiderRegionArg.class;
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Helper Classes">
    private class AddFeetTransformer extends IdTransformer {

        private final SpiderRegionArg arg;

        public AddFeetTransformer(SpiderRegionArg arg) {
            this.arg = arg;
        }

        @Override
        public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) {
            // Transform only the target diagram
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // Okay, we are at the diagram we want to change. Now make some
                // checks: that the arguments are correct and make sense.
                Region splitRegion = arg.getRegion();
                if (splitRegion == null) {
                    throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "arg.getRegion()"));
                }
                if (arg.getSpider() == null) {
                    throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "arg.getSpider()"));
                }
                if (!psd.containsSpider(arg.getSpider())) {
                    throw new IllegalArgumentException(i18n("ERR_SPIDER_NOT_IN_DIAGRAM", arg.getSpider()));
                }
                Region habitat = psd.getSpiderHabitat(arg.getSpider());
                // Check that the splitRegion is a proper subregion of the
                // spider's habitat.
                if (splitRegion.isSubregionOf(habitat) && splitRegion.getZonesCount() < habitat.getZonesCount() && splitRegion.getZonesCount() > 0) {
                    // The checking of arguments is done. We may apply the rule.
                    done = true;
                    ArrayList<SpiderDiagram> sds = new ArrayList<SpiderDiagram>();
                    sds.add(psd.changeSpiderHabitat(arg.getSpider(), splitRegion));
                    sds.add(psd.changeSpiderHabitat(arg.getSpider(), habitat.subtract(splitRegion)));
                    return SpiderDiagrams.createCompoundSD(Operator.OP_NAME_OR, sds, false);
                } else {
                    throw new IllegalArgumentException(i18n("ERR_SPLIT_SPIDERS_INVALID_REGION"));
                }
            }
            return null;
        }
    }
    //</editor-fold>
}
