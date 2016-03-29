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

import speedith.core.i18n.Translations;
import speedith.core.lang.*;
import speedith.core.reasoning.*;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.rules.instructions.AddFeetRuleInstruction;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

import static speedith.core.i18n.Translations.i18n;

/**
 * The implementation of the 'add feet' inference rule. <p>The argument to this
 * inference rule is a {@link SpiderRegionArg
 * spider-region argument}, which tells the rule into which zones to add new
 * feet of a particular spider.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class AddFeet extends SimpleInferenceRule<SpiderRegionArg> implements BasicInferenceRule<SpiderRegionArg>, ForwardRule<SpiderRegionArg>, Serializable {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    /**
     * The name of this inference rule. <p>This value is returned by the
     * {@link AddFeet#getInferenceName()} method.</p>
     */
    public static final String InferenceRuleName = "add_feet";

    private static final Set<DiagramType> applicableTo = EnumSet.of(DiagramType.SpiderDiagram);
    private static final long serialVersionUID = 3758267039172032810L;
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="InferenceRule Implementation">
    @Override
    public RuleApplicationResult apply(final RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals, false);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="ForwardRule Implementation">
    @Override
    public RuleApplicationResult applyForwards(RuleArg args, Goals goals) throws RuleApplicationException {
        return apply(args, goals, true);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="InferenceRuleProvider Implementation">
    @Override
    public AddFeet getInferenceRule() {
        return this;
    }

    @Override
    public String getInferenceName() {
        return InferenceRuleName;
    }

    @Override
    public String getDescription(Locale locale) {
        return i18n(locale, "ADD_FEET_DESCRIPTION");
    }

    @Override
    public String getCategory(Locale locale) {
        return i18n(locale, "INF_RULE_CATEGORY_PURELY_DIAGRAMMATIC");
    }

    @Override
    public String getPrettyName(Locale locale) {
        return i18n(locale, "ADD_FEET_PRETTY_NAME");
    }

    @Override
    public Class<SpiderRegionArg> getArgumentType() {
        return SpiderRegionArg.class;
    }

    @Override
    public RuleApplicationInstruction<SpiderRegionArg> getInstructions() {
        return AddFeetRuleInstruction.getInstance();
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTo;
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="The general 'apply' method">
    private RuleApplicationResult apply(final RuleArg args, Goals goals, boolean applyForward) throws RuleApplicationException {
        SpiderRegionArg arg = getTypedRuleArgs(args);
        SpiderDiagram[] newSubgoals = goals.getGoals().toArray(new SpiderDiagram[goals.getGoalsCount()]);
        newSubgoals[arg.getSubgoalIndex()] = getSubgoal(arg, goals).transform(new AddFeetTransformer(arg, applyForward));
        return createRuleApplicationResult(newSubgoals);
    }
    //</editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Helper Classes">
    private class AddFeetTransformer extends IdTransformer {

        private final SpiderRegionArg arg;
        private final boolean applyForward;

        public AddFeetTransformer(SpiderRegionArg arg, boolean applyForward) {
            this.arg = arg;
            this.applyForward = applyForward;
        }

        @Override
        public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
            // Transform only the target diagram
            if (diagramIndex == arg.getSubDiagramIndex()) {
                // Okay, we are at the diagram we want to change. Now make some
                // checks: that the arguments are correct and make sense.
                Region feetToAdd = arg.getRegion();
                if (feetToAdd == null) {
                    throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "arg.getRegion()"));
                }
                if (arg.getSpider() == null) {
                    throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "arg.getSpider()"));
                }
                if (!psd.containsSpider(arg.getSpider())) {
                    throw new IllegalArgumentException(i18n("ERR_SPIDER_NOT_IN_DIAGRAM", arg.getSpider()));
                }
                // Are we applying this rule in a forward way or backward way?
                if (applyForward
                        ? !isAtPositivePosition(parents, childIndices)
                        : !isAtNegativePosition(parents, childIndices)) {
                    throw new TransformationException(Translations.i18n("GERR_RULE_WRONG_POSITION"));
                }
                // Now make sure that the spider actually exists in the diagram:
                Region existingFeet = psd.getSpiderHabitat(arg.getSpider());
                if (existingFeet == null || existingFeet.getZonesCount() < 1) {
                    throw new TransformationException(i18n("ADD_FEET_INVALID_APPLICATION_POINT"));
                }
                // Now make a union of the two regions
                Region withAddedFeet = existingFeet.union(feetToAdd);
                done = true;
                return psd.addSpider(arg.getSpider(), withAddedFeet);
            }
            return null;
        }
    }
    //</editor-fold>
}
