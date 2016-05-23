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

import speedith.core.lang.DiagramType;
import speedith.core.lang.IdTransformer;
import speedith.core.lang.Transformer;
import speedith.core.reasoning.ApplyStyle;
import speedith.core.reasoning.RuleApplicationInstruction;
import speedith.core.reasoning.args.SubDiagramIndexArg;

import java.io.Serializable;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Set;

/**
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ExcludedMiddle extends UnaryForwardRule implements Serializable {

    public static final String InferenceRuleName = "Excluded Middle";

    private static final Set<DiagramType> applicableTypes = EnumSet.of(DiagramType.SpiderDiagram);
    private static final long serialVersionUID = 7841176724648588879L;

    @Override
    protected Transformer getSententialTransformer(SubDiagramIndexArg arg, ApplyStyle applyStyle) {
        return new IdTransformer();
    }

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
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }
}
