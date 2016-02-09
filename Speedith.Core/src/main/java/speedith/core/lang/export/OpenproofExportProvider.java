/*
 *   Project: Speedith.Core
 * 
 * File name: Isabelle2011ExportProvider.java
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
package speedith.core.lang.export;

import speedith.core.lang.*;

import java.io.IOException;
import java.io.Writer;
import java.util.*;

import static speedith.core.i18n.Translations.i18n;

/**
 * The provider for exporting spider diagrams to Openproof's FOL formulae.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class OpenproofExportProvider extends SDExportProvider {

    /**
     * The name of the export format of this provider.
     */
    public static final String FormatName = "Openproof";

    @Override
    public String getFormatName() {
        return FormatName;
    }

    @Override
    public SDExporter getExporter(Map<String, String> parameters) {
        return Exporter.Instance;
    }

    @Override
    public String getDescription(Locale locale) {
        return i18n(locale, "OPENPROOF_EXPORT_DESCRIPTION");
    }

    @Override
    public SortedSet<String> getParameters() {
        return Collections.unmodifiableSortedSet(ParameterDescriptions.Parameters.navigableKeySet());
    }

    @Override
    public String getParameterDescription(String parameter, Locale locale) {
        return i18n(locale, ParameterDescriptions.Parameters.get(parameter));
    }

    /**
     * The actual exporter class. This class does the actual translation from
     * spider diagrams to Isabelle's formulas.
     */
    private static class Exporter extends SDExporter {

        // <editor-fold defaultstate="collapsed" desc="Fields">
        static final Exporter Instance = new Exporter();
        // </editor-fold>
        // <editor-fold defaultstate="collapsed" desc="Constructors">

        public Exporter() {
        }
        // </editor-fold>

        // <editor-fold defaultstate="collapsed" desc="Isabelle Symbol/Operator Print Methods">
        private static Writer printAnd(Writer output) throws IOException {
            return output.append(' ').append("&").append(' ');
        }

        private static Writer printOr(Writer output) throws IOException {
            return output.append(' ').append("|").append(' ');
        }

        private static Writer printNeg(Writer output) throws IOException {
            return output.append(' ').append("~");
        }

        private static Writer printElementOf(Writer output) throws IOException {
            return output.append(' ').append("\\").append(' ');
        }

        private Writer printUnion(Writer output) throws IOException {
            return output.append(' ').append("union");
        }

        private Writer printIntersection(Writer output) throws IOException {
            return output.append(' ').append("inter").append(' ');
        }

        private Writer printSubsetEq(Writer output) throws IOException {
            return output.append(' ').append("_").append(' ');
        }

        private static Writer printImp(Writer output) throws IOException {
            return output.append(' ').append("$").append(' ');
        }

        private static Writer printEquiv(Writer output) throws IOException {
            return output.append(' ').append("%").append(' ');
        }

        private static Writer printTrue(Writer output) throws IOException {
            // TODO: Is this the right 'truth' constant in Openproof?
            return output.append("True");
        }

        private static Writer printExists(Writer output) throws IOException {
            return output.append("/");
        }

        private static Writer printUniversalSet(Writer output) throws IOException {
            return output.append("UNIV");
        }

        private static Writer printOpeningParenthesis(Writer output) throws IOException {
            return output.append("(");
        }

        private static Writer printClosingParenthesis(Writer output) throws IOException {
            return output.append(")");
        }

        private static Writer printInequality(Writer output) throws IOException {
            return output.append(" # ");
        }
        // </editor-fold>

        // <editor-fold defaultstate="collapsed" desc="Export Methods">
        @Override
        public void exportTo(SpiderDiagram sd, Writer output) throws IOException, ExportException {
            if (output == null) {
                throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "output"));
            }
            exportDiagram(sd, output);
            output.flush();
        }

        private void exportNullDiagram(Writer output) throws IOException {
            printTrue(output);
        }

        private void exportInfixOperator(CompoundSpiderDiagram nsd, Writer output, PrintCallback operatorSymbolPrinter) throws IOException, RuntimeException {
            // We have to print an infix operator application.
            if (nsd.getOperandCount() < 2) {
                throw new RuntimeException(i18n("ERR_EXPORT_ARG_COUNT_INVALID", nsd.getOperandCount()));
            } else {
                // Print out the first operand and enclose it in parentheses.
                // All the operands must be enclosed in parentheses because
                // Openproof requires it.
                printOpeningParenthesis(output);
                exportDiagram(nsd.getOperand(0), output);
                printClosingParenthesis(output);
                for (int i = 1; i < nsd.getOperandCount(); i++) {
                    // Print the operator simbol (with spaces around it).
                    operatorSymbolPrinter.print(output);

                    // Print the other operands and enclose them in parentheses.
                    printOpeningParenthesis(output);
                    exportDiagram(nsd.getOperand(i), output);
                    printClosingParenthesis(output);
                }
            }
        }

        private void exportDiagram(SpiderDiagram sd, Writer output) throws IOException {
            if (sd instanceof NullSpiderDiagram) {
                exportNullDiagram(output);
            } else if (sd instanceof CompoundSpiderDiagram) {
                exportCompoundDiagram((CompoundSpiderDiagram) sd, output);
            } else if (sd instanceof PrimarySpiderDiagram) {
                exportPrimaryDiagram((PrimarySpiderDiagram) sd, output);
            } else {
                throw new IllegalArgumentException(i18n("ERR_EXPORT_INVALID_SD"));
            }
        }

        private void exportCompoundDiagram(CompoundSpiderDiagram csd, Writer output) throws IOException {
            // TODO: Implement the negation too.
            final Operator op = csd.getOperator();
            if (op.equals(Operator.Implication.getName())) {
                exportInfixOperator(csd, output, ImpOperatorPrinter.Instance);
            } else if (op.equals(Operator.Conjunction.getName())) {
                exportInfixOperator(csd, output, AndOperatorPrinter.Instance);
            } else if (op.equals(Operator.Disjunction.getName())) {
                exportInfixOperator(csd, output, OrOperatorPrinter.Instance);
            } else if (op.equals(Operator.Equivalence.getName())) {
                exportInfixOperator(csd, output, EqOperatorPrinter.Instance);
            } else {
                throw new RuntimeException(i18n("GERR_ILLEGAL_STATE"));
            }
        }

        private void exportPrimaryDiagram(PrimarySpiderDiagram psd, Writer output) throws IOException {
            SortedSet<String> spiders = psd.getSpiders();
            // Existentially quantify all spiders. After each existential
            // quantifier a parenthesis must follow.
            Iterator<String> itr = spiders.iterator();
            while (itr.hasNext()) {
                printExists(output).append(itr.next());
                printOpeningParenthesis(output);
            }

            // Print the distinct term, but only if there are more than one spiders.
            final boolean printedDistinct = psd.getSpidersCount() > 1;
            if (printedDistinct) {
                printOpeningParenthesis(output);
                exportSpidersDistinct(psd, output);
                printClosingParenthesis(output);
                printAnd(output);
            }

            if (psd.getHabitatsCount() < 1 && psd.getShadedZonesCount() < 1) {
                printTrue(output);
            } else {
                exportHabitats(psd, output);
                exportShadedZones(psd, output, spiders);
            }
            for (int i = spiders.size(); i > 0; i--) {
                printClosingParenthesis(output);
            }
        }

        private void exportShadedZones(PrimarySpiderDiagram psd, Writer output, SortedSet<String> spiders) throws IOException {
            if (psd.getShadedZonesCount() > 0) {
                // TODO: Implement
//                throw new UnsupportedOperationException();
//                SortedSet<Zone> shadedZones = psd.getShadedZones();
//                Iterator<Zone> itr = shadedZones.iterator();
//                Zone zone = itr.next();
//                exportZone(zone, output);
//                printSubsetEq(output);
//                Sets.printSet(spiders, output);
            }
        }

        /**
         * Returns {@code true} iff at least one term was printed to the output.
         *
         * @throws IOException
         */
        private boolean exportHabitats(PrimarySpiderDiagram psd, Writer output) throws IOException {
            if (psd.getHabitatsCount() > 0) {
                SortedMap<String, Region> habitats = psd.getHabitats();
                Iterator<String> itr = habitats.keySet().iterator();

                // Print out all the habitats for all the spiders.
                exportHabitat(output, itr.next(), habitats);
                while (itr.hasNext()) {
                    printAnd(output);
                    exportHabitat(output, itr.next(), habitats);
                }
                return true;
            } else {
                return false;
            }
        }

        private void exportSpidersDistinct(PrimarySpiderDiagram psd, Writer output) throws IOException {
            if (psd.getSpidersCount() > 1) {
                SortedSet<String> spiderSet = psd.getSpiders();
                String[] spiders = spiderSet.toArray(new String[spiderSet.size()]);
                for (int i = 0; i < spiders.length; i++) {
                    String spiderA = spiders[i];
                    for (int j = i + 1; j < spiders.length; j++) {
                        // Don't print the AND operator if we are printing the
                        // first inequality
                        if (i > 0 || j > 1) {
                            printAnd(output);
                        }

                        // Print parentheses if there will be more than one inequality
                        if (spiders.length > 2) {
                            printOpeningParenthesis(output);
                        }

                        output.append(spiderA);
                        printInequality(output).append(spiders[j]);

                        if (spiders.length > 2) {
                            printClosingParenthesis(output);
                        }
                    }
                }
            }
        }

        private void exportHabitat(Writer output, String spider, SortedMap<String, Region> habitats) throws IOException {
            exportHabitat(spider, habitats.get(spider), output);
        }

        private void exportHabitat(String spider, Region region, Writer output) throws IOException {
            SortedSet<Zone> zones = region.sortedZones();
            if (zones.isEmpty()) {
                printOpeningParenthesis(output);
                printUniversalSet(output).append("(").append(spider).append(")");
                printClosingParenthesis(output);
            } else {
                Iterator<Zone> itr = zones.iterator();

                // We print parentheses only if we know there will be operators
                // other than AND. So, if there will be more than one zone, we
                // will have to put in OR operators... Thus, requiring
                // parentheses.
                boolean printParens = zones.size() > 1;

                if (printParens) {
                    printOpeningParenthesis(output);
                }
                int counter = 0;
                while (itr.hasNext()) {
                    // If a region contains more zones, we will have to print
                    // them with disjunction. We may print the disjunction only
                    // after the first operand and just before the following ones.
                    if (counter > 0) {
                        printOr(output);
                    }
                    if (printParens) {
                        printOpeningParenthesis(output);
                    }
                    exportZone(spider, itr.next(), output);
                    if (printParens) {
                        printClosingParenthesis(output);
                    }
                    counter++;
                }
                if (printParens) {
                    printClosingParenthesis(output);
                }
            }
        }

        private void exportZone(String spider, Zone zone, Writer output) throws IOException {
            SortedSet<String> inContours = zone.getInContours();
            SortedSet<String> outContours = zone.getOutContours();
            boolean printedSome = false;
            Iterator<String> iter;
            if (inContours != null) {
                iter = inContours.iterator();
                while (iter.hasNext()) {
                    if (printedSome) {
                        printAnd(output);
                    }
                    output.append(iter.next()).append("(").append(spider).append(")");
                    printedSome = true;
                }
            }
            if (outContours != null) {
                iter = outContours.iterator();
                while (iter.hasNext()) {
                    if (printedSome) {
                        printAnd(output);
                    }
                output.append("~").append(iter.next()).append("(").append(spider).append(")");
                    printedSome = true;
                }
            }
        }
        // </editor-fold>

        // <editor-fold defaultstate="collapsed" desc="Helper Classes">
        private static class EqOperatorPrinter implements PrintCallback {

            static final EqOperatorPrinter Instance = new EqOperatorPrinter();

            @Override
            public void print(Writer output) throws IOException {
                printEquiv(output);
            }
        }

        private static class OrOperatorPrinter implements PrintCallback {

            static final OrOperatorPrinter Instance = new OrOperatorPrinter();

            @Override
            public void print(Writer output) throws IOException {
                printOr(output);
            }
        }

        private static class AndOperatorPrinter implements PrintCallback {

            static final AndOperatorPrinter Instance = new AndOperatorPrinter();

            @Override
            public void print(Writer output) throws IOException {
                printAnd(output);
            }
        }

        private static class ImpOperatorPrinter implements PrintCallback {

            static final ImpOperatorPrinter Instance = new ImpOperatorPrinter();

            @Override
            public void print(Writer output) throws IOException {
                printImp(output);
            }
        }
        // </editor-fold>
    }

    // <editor-fold defaultstate="collapsed" desc="Parameter Descriptions">
    private static final class ParameterDescriptions {

        public static final TreeMap<String, String> Parameters;

        static {
            Parameters = new TreeMap<>();
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Callback Interfaces">
    private static interface PrintCallback {

        void print(Writer output) throws IOException;
    }
    // </editor-fold>
}
