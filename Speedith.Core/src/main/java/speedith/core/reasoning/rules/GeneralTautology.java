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
 * TODO: The general tautology inference rule would be nice to have. It's not
 * yet implemented.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class GeneralTautology extends UnaryForwardRule implements Serializable {

    public static final String InferenceRuleName = "general_tautology";

    private static final Set<DiagramType> applicableTypes = EnumSet.noneOf(DiagramType.class);
    private static final long serialVersionUID = -5205748212133960769L;

    @Override
    public String getInferenceName() {
        return InferenceRuleName;
    }

    @Override
    public String getDescription(Locale locale) {
        return "This inference rule replaces tautological compound spider diagrams with null spider diagrams. It handles the typical tautologies for logical connectives.";
    }

    @Override
    public String getPrettyName(Locale locale) {
        return "Tautology";
    }

    @Override
    public RuleApplicationInstruction<SubDiagramIndexArg> getInstructions() {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    protected Transformer getSententialTransformer(SubDiagramIndexArg arg, ApplyStyle applyStyle) {
        return new IdTransformer();
    }

    @Override
    public Set<DiagramType> getApplicableTypes() {
        return applicableTypes;
    }
}
