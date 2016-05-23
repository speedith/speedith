/*
 *   Project: Speedith.Core
 * 
 * File name: GeneralTautology.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2013 Matej Urbas
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

import speedith.core.lang.*;
import speedith.core.lang.util.CompoundDiagramsUtils;
import speedith.core.lang.util.HabitatUtils;
import speedith.core.lang.util.ShadingUtils;
import speedith.core.reasoning.ApplyStyle;
import speedith.core.reasoning.RuleApplicationInstruction;
import speedith.core.reasoning.args.SubDiagramIndexArg;
import speedith.core.reasoning.rules.instructions.SelectSingleOperatorInstruction;
import speedith.core.reasoning.rules.util.CombiningUtils;

import java.io.Serializable;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Combining extends UnaryForwardRule implements Serializable {

  public static final String InferenceRuleName = "Combining";

  private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.EulerDiagram, DiagramType.SpiderDiagram);
  private static final long serialVersionUID = -1556054106670781741L;


  @Override
  public String getInferenceName() {
    return InferenceRuleName;
  }

  @Override
  public String getDescription(Locale locale) {
    return "";
  }

  @Override
  public String getPrettyName(Locale locale) {
    return InferenceRuleName;
  }

  @Override
  public RuleApplicationInstruction<SubDiagramIndexArg> getInstructions() {
    return new SelectSingleOperatorInstruction(Operator.Conjunction);
  }

  @Override
  protected Transformer getSententialTransformer(SubDiagramIndexArg arg, ApplyStyle applyStyle) {
    return new CombiningTransformer(arg, applyStyle);
  }

  private class CombiningTransformer extends UnaryForwardTransformer {

    public CombiningTransformer(SubDiagramIndexArg arg, ApplyStyle applyStyle) {
      super(arg, applyStyle);
    }

    @Override
    protected SpiderDiagram apply(CompoundSpiderDiagram csd) {
      if (CompoundDiagramsUtils.isConjunctionOfPrimaryDiagrams(csd)) {
        return Combining.apply((PrimarySpiderDiagram) csd.getOperand(0), (PrimarySpiderDiagram) csd.getOperand(1));
      }
      return unsupported();
    }

    @Override
    protected SpiderDiagram unsupported() {
      throw new TransformationException("Could not apply the 'combining' rule. This rule may be applied only on a conjunction of two unitary diagrams.");
    }
  }

  @Override
  public Set<DiagramType> getApplicableTypes() {
    return applicableTypes;
  }

  public static SpiderDiagram apply(PrimarySpiderDiagram leftDiagram, PrimarySpiderDiagram rightDiagram) {
    if (!leftDiagram.getAllContours().equals(rightDiagram.getAllContours())) {
      throw new TransformationException("Could not apply the 'combining' rule. The unitary diagrams do not contain the same contours.");
    }
    if (!HabitatUtils.habitatsAreSingleZoned(leftDiagram) || !HabitatUtils.habitatsAreSingleZoned(rightDiagram)) {
      throw new TransformationException("Could not apply the 'combining' rule. The unitary diagrams contain spiders with multi-zoned habitats.");
    }
    if (!ShadingUtils.allShadedZonesHaveSameSpidersAsShadedZonesInOther(leftDiagram, rightDiagram) ||
        ShadingUtils.anyShadedZoneHasFewerSpidersThanNonShadedZoneInOther(leftDiagram, rightDiagram) ||
        ShadingUtils.anyShadedZoneHasFewerSpidersThanNonShadedZoneInOther(rightDiagram, leftDiagram)) {
      return SpiderDiagrams.bottom();
    }
    return CombiningUtils.combine(leftDiagram, rightDiagram);
  }
}
