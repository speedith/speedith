/*
 *   Project: Speedith.Core
 * 
 * File name: SplitSpiders.java
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

import java.util.ArrayList;
import java.util.Locale;
import static speedith.core.i18n.Translations.*;
import speedith.core.lang.*;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.rules.instructions.SelectFeetOfSpiderInstruction;

/**
 * The implementation of the 'split spiders' diagrammatic inference rule.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SplitSpiders extends SimpleInferenceRule<SpiderRegionArg> implements BasicInferenceRule<SpiderRegionArg>, ForwardRule<SpiderRegionArg>, BackwardRule<SpiderRegionArg> {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The name of this inference rule. <p>This value is returned by the {@link SplitSpiders#getInferenceRuleName()}
     * method.</p>
     */
    public static final String InferenceRuleName = "split_spiders";
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        SpiderRegionArg arg = getTypedRuleArgs(args);
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(new SplitSpiderTransformer(arg), false);
        return new RuleApplicationResult(Goals.createGoalsFrom(newSubgoals));
    }
    //</editor-fold>

    // <editor-fold defaultstate="collapsed" desc="InferenceRuleProvider Implementation">
    public SplitSpiders getInferenceRule() {
        return this;
    }

    public String getInferenceRuleName() {
        return InferenceRuleName;
    }

    public String getDescription(Locale locale) {
        return i18n(locale, "SPLIT_SPIDERS_DESCRIPTION");
    }

    public String getPrettyName(Locale locale) {
        return i18n(locale, "SPLIT_SPIDERS_PRETTY_NAME");
    }

    public Class<SpiderRegionArg> getArgumentType() {
        return SpiderRegionArg.class;
    }

    public RuleApplicationInstruction<SpiderRegionArg> getInstructions() {
        return SelectFeetOfSpiderInstruction.getInstance();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="ForwardRule Implementation">
    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="BackwardRule Implementation">
    @Override
    public RuleApplicationResult applyBackwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals);
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Helper Classes">
    private class SplitSpiderTransformer extends IdTransformer {

        private final SpiderRegionArg arg;

        public SplitSpiderTransformer(SpiderRegionArg arg) {
            this.arg = arg;
        }

        @Override
        public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
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
                    sds.add(psd.addSpider(arg.getSpider(), splitRegion));
                    sds.add(psd.addSpider(arg.getSpider(), habitat.subtract(splitRegion)));
                    return SpiderDiagrams.createCompoundSD(Operator.Disjunction, sds, false);
                } else {
                    throw new IllegalArgumentException(i18n("ERR_SPLIT_SPIDERS_INVALID_REGION"));
                }
            }
            return null;
        }
    }
    //</editor-fold>
}
