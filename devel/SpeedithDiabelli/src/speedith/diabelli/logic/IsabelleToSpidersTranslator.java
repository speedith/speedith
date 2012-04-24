/*
 * File name: IsabelleToSpidersTranslator.java
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
package speedith.diabelli.logic;

import diabelli.isabelle.terms.TermFormatDescriptor;
import diabelli.logic.Formula;
import diabelli.logic.FormulaRepresentation;
import diabelli.logic.FormulaTranslator;
import isabelle.Term;
import java.util.ArrayList;
import java.util.List;
import org.openide.util.NbBundle;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.reader.ReadingException;

/**
 * This translator is able to translate {@link isabelle.Term.Term Isabelle terms}
 * to {@link SpiderDiagram spider diagrams}.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@NbBundle.Messages({
    "ISAtoSDTrans_internal_name=IsabelleTerms_to_SpiderDiagrams"
})
public class IsabelleToSpidersTranslator extends FormulaTranslator<Term.Term, SpiderDiagram> {

    // <editor-fold defaultstate="collapsed" desc="Singleton stuff">
    private IsabelleToSpidersTranslator() {
        super(TermFormatDescriptor.getInstance(), SpeedithFormatDescriptor.getInstance(), TranslationType.ToEquivalent, Bundle.ISAtoSDTrans_internal_name());
    }

    public static IsabelleToSpidersTranslator getInstance() {
        return SingletonContainer.Instance;
    }

    private static class SingletonContainer {

        private static final IsabelleToSpidersTranslator Instance = new IsabelleToSpidersTranslator();
    }
    // </editor-fold>

    @Override
    @NbBundle.Messages({
        "ISAtoSDTrans_description=Translation of Isabelle terms formulae to spider diagrams."
    })
    public String getDescription() {
        return Bundle.ISAtoSDTrans_description();
    }

    @Override
    @NbBundle.Messages({
        "ISAtoSDTrans_pretty_name=Isabelle terms to spider diagrams"
    })
    public String getPrettyName() {
        return Bundle.ISAtoSDTrans_pretty_name();
    }

    @Override
    @NbBundle.Messages({
        "ISAtoSDTrans_translation_error_no_isa_term=The formula does not have an Isabelle term representation.",
        "ISAtoSDTrans_translation_error_reading_failed=The Isabelle formula is not of the format that can be translated to spider diagrams.",
        "ISAtoSDTrans_translation_error_isa_formula_not_a_term=The Isabelle driver might be faulty. It returned an Isabelle term formula that is not a Term.Term.",
        "ISAtoSDTrans_translation_error_null_sd_returned=The translation failed to produce a valid spider diagram."
    })
    public Formula<SpiderDiagram> translate(Formula<Term.Term> formula) throws TranslationException {
        FormulaRepresentation[] isaRepresentations = formula.fetchRepresentations(TermFormatDescriptor.getInstance());
        if (isaRepresentations == null || isaRepresentations.length == 0) {
            throw new TranslationException(Bundle.ISAtoSDTrans_translation_error_no_isa_term());
        }
        if (isaRepresentations[0].getFormula() instanceof Term.Term) {
            Term.Term term = (Term.Term) isaRepresentations[0].getFormula();
            try {
                SpiderDiagram sd = speedith.diabelli.isabelle.Translations.termToSpiderDiagram(term);
                if (sd == null || !sd.isValid()) {
                    throw new TranslationException(Bundle.ISAtoSDTrans_translation_error_null_sd_returned());
                }
                return new Formula<>(new FormulaRepresentation<>(sd, SpeedithFormatDescriptor.getInstance()), formula.getRole());
            } catch (ReadingException ex) {
                throw new TranslationException(Bundle.ISAtoSDTrans_translation_error_reading_failed(), ex);
            }
        } else {
            throw new IllegalStateException();
        }
    }

    @Override
    public ArrayList<Formula<SpiderDiagram>> translate(List<Formula<Term.Term>> formulae) throws TranslationException {
        throw new UnsupportedOperationException("Not supported yet.");
    }
}
