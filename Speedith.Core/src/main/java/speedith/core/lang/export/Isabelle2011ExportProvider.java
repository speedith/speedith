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

import propity.util.Sequences;
import propity.util.Sets;
import speedith.core.lang.*;

import java.io.IOException;
import java.io.Writer;
import java.util.*;

import static speedith.core.i18n.Translations.i18n;

/**
 * The provider for exporting spider diagrams to Isabelle 2011 formulae.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Isabelle2011ExportProvider extends SDExportProvider {

    /**
     * The name of the export format of this provider.
     */
    public static final String FormatName = "Isabelle2011";
    public static final String Parameter_ML = "ml";
    public static final String Parameter_UseXSymbols = "useXSymbols";

    @Override
    public String getFormatName() {
        return FormatName;
    }

    @Override
    public SDExporter getExporter(Map<String, String> parameters) {
        boolean useXSymbols = "true".equalsIgnoreCase(parameters == null ? null : parameters.get(Parameter_UseXSymbols));
        boolean useML = "true".equalsIgnoreCase(parameters == null ? null : parameters.get(Parameter_ML));
        return new Exporter(useXSymbols, useML);
    }

    @Override
    public String getDescription(Locale locale) {
        return i18n(locale, "ISABELE_EXPORT_DESCRIPTION");
    }

    @Override
    public SortedSet<String> getParameters() {
        return Collections.unmodifiableSortedSet(ParameterDescriptions.Parameters.navigableKeySet());
    }

    @Override
    public String getParameterDescription(String parameter, Locale locale) {
        return i18n(locale, ParameterDescriptions.Parameters.get(parameter));
    }

    private static interface PrintCallback {

        void print(Writer output) throws IOException;
    }

    /**
     * The actual exporter class. This class does the actual translation from
     * spider diagrams to Isabelle's formulas.
     */
    private static class Exporter extends SDExporter {

        // TODO: Maybe I should write a generic pretty
        // printer, which takes into account precedence order of operators in
        // Isabelle automatically?
        public static final String ISA_SYM_EX = "EX";
        public static final String ISA_XSYM_EXISTS = "∃";
        private boolean useXSymbols;
        private boolean useML;

        public Exporter() {
            this(false, false);
        }

        public Exporter(boolean useXSymbols, boolean useML) {
            this.useXSymbols = useXSymbols;
            this.useML = useML;
        }

        @Override
        public void exportTo(SpiderDiagram sd, Writer output) throws IOException, ExportException {
            if (output == null) {
                throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "output"));
            }
            if (useML) {
                exportDiagramML(sd, output);
            } else {
                exportDiagram(sd, output);
            }
            output.flush();
        }

        private Writer printAnd(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<and>").append(' ');
            } else {
                return output.append(' ').append("&").append(' ');
            }
        }

        private Writer printOr(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<or>").append(' ');
            } else {
                return output.append(' ').append("|").append(' ');
            }
        }

        private Writer printNeg(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<not>").append(' ');
            } else {
                return output.append(' ').append("~").append(' ');
            }
        }

        private Writer printElementOf(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<in>").append(' ');
            } else {
                return output.append(' ').append(":").append(' ');
            }
        }

        private Writer printUnion(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<union>").append(' ');
            } else {
                return output.append(' ').append("Un").append(' ');
            }
        }

        private Writer printIntersection(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<inter>").append(' ');
            } else {
                return output.append(' ').append("Int").append(' ');
            }
        }

        private Writer printSubsetEq(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<subseteq>").append(' ');
            } else {
                return output.append(' ').append("<=").append(' ');
            }
        }

        private Writer printImp(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<longrightarrow>").append(' ');
            } else {
                return output.append(' ').append("-->").append(' ');
            }
        }

        private Writer printEquiv(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<longleftrightarrow>").append(' ');
            } else {
                return output.append(' ').append("<-->").append(' ');
            }
        }

        private Writer printTrue(Writer output) throws IOException {
            return output.append("True");
        }

        private Writer printExists(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append("\\<exists>");
            } else {
                return output.append(ISA_SYM_EX).append(' ');
            }
        }

        private Writer printMLAll(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append("\\<And>");
            } else {
                return output.append("!!");
            }
        }

        private Writer printMLLeftBracket(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append("\\<lbrakk>");
            } else {
                return output.append("[|");
            }
        }

        private Writer printMLRightBracket(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append("\\<rbrakk>");
            } else {
                return output.append("|]");
            }
        }

        private Writer printMLSemiCollon(Writer output) throws IOException {
            return output.append("; ");
        }

        private Writer printMLImplication(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(" ").append("\\<Longrightarrow>").append(' ');
            } else {
                return output.append(' ').append("==>").append(' ');
            }
        }

        private Writer printUniversalSet(Writer output) throws IOException {
            return output.append("UNIV");
        }

        private void printHolOrMlAnd(Writer output, boolean useML) throws IOException {
            if (useML) {
                printMLSemiCollon(output);
            } else {
                printAnd(output);
            }
        }

        private void exportNullDiagram(Writer output) throws IOException {
            printTrue(output);
        }

        private void exportInfixOperator(CompoundSpiderDiagram nsd, Writer output, PrintCallback operatorSymbolPrinter) throws IOException, RuntimeException {
            // We have to print an infix operator application.
            if (nsd.getOperandCount() < 2) {
                throw new RuntimeException(i18n("ERR_EXPORT_ARG_COUNT_INVALID", nsd.getOperandCount()));
            } else {
                exportDiagram(nsd.getOperand(0), output);
                for (int i = 1; i < nsd.getOperandCount(); i++) {
                    operatorSymbolPrinter.print(output);
                    exportDiagram(nsd.getOperand(i), output);
                }
            }
        }

        private void exportCompoundDiagram(CompoundSpiderDiagram nsd, Writer output) throws IOException {
            final Operator op = nsd.getOperator();
            if (op.equals(Operator.Implication.getName())) {
                exportInfixOperator(nsd, output, new ImpOperatorPrinter());
            } else if (op.equals(Operator.Conjunction.getName())) {
                exportInfixOperator(nsd, output, new AndOperatorPrinter());
            } else if (op.equals(Operator.Disjunction.getName())) {
                exportInfixOperator(nsd, output, new OrOperatorPrinter());
            } else if (op.equals(Operator.Equivalence.getName())) {
                exportInfixOperator(nsd, output, new EqOperatorPrinter());
            } else {
                throw new RuntimeException(i18n("GERR_ILLEGAL_STATE"));
            }
        }

        private void exportPrimaryDiagram(PrimarySpiderDiagram psd, Writer output) throws IOException {
            output.append('(');
            SortedSet<String> spiders = psd.getSpiders();
            exportExistsHeader(psd, output, spiders);
            exportSpidersDistinct(psd, output, false);
            if (psd.getHabitatsCount() < 1 && psd.getShadedZonesCount() < 1) {
                printTrue(output);
            } else {
                exportHabitats(psd, output, false);
                exportShadedZones(psd, output, spiders);
            }
            output.append(')');
        }

        private void exportExistsHeader(PrimarySpiderDiagram psd, Writer output, SortedSet<String> spiders) throws IOException {
            if (psd.getSpidersCount() > 0) {
                Iterator<String> itr = spiders.iterator();
                printExists(output).append(itr.next());
                while (itr.hasNext()) {
                    output.append(' ').append(itr.next());
                }
                output.append(". ");
            }
        }

        private void exportShadedZones(PrimarySpiderDiagram psd, Writer output, SortedSet<String> spiders) throws IOException {
            if (psd.getShadedZonesCount() > 0) {
                SortedSet<Zone> shadedZones = psd.getShadedZones();
                Iterator<Zone> itr = shadedZones.iterator();
                exportShadedZone(output, spiders, itr.next());
                while (itr.hasNext()) {
                    printHolOrMlAnd(output, useML);
                    exportShadedZone(output, spiders, itr.next());
                }
            }
        }

        private void exportShadedZone(Writer output, SortedSet<String> spiders, Zone zone) throws IOException {
            exportZone(zone, output);
            printSubsetEq(output);
            Sets.printSet(spiders, output);
        }

        private void exportHabitats(PrimarySpiderDiagram psd, Writer output, boolean useML) throws IOException {
            if (psd.getHabitatsCount() > 0) {
                SortedMap<String, Region> habitats = psd.getHabitats();
                Iterator<String> itr = habitats.keySet().iterator();
                String spider = itr.next();
                exportHabitat(spider, habitats.get(spider), output);
                while (itr.hasNext()) {
                    spider = itr.next();
                    printHolOrMlAnd(output, useML);
                    exportHabitat(spider, habitats.get(spider), output);
                }
                if (psd.getShadedZonesCount() > 0) {
                    printHolOrMlAnd(output, useML);
                }
            }
        }

        private void exportSpidersDistinct(PrimarySpiderDiagram psd, Writer output, boolean useML) throws IOException {
            if (psd.getSpidersCount() > 1) {
                output.append("distinct");
                Sequences.print(psd.getSpiders(), output, "[", "]", ", ");
                printHolOrMlAnd(output, useML);
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

        private void exportDiagramML(SpiderDiagram sd, Writer output) throws ExportException, IOException {
            if (sd instanceof CompoundSpiderDiagram) {
                CompoundSpiderDiagram csd = (CompoundSpiderDiagram) sd;
                if (csd.getOperator().equals(Operator.Implication)) {
                    final SpiderDiagram op1 = csd.getOperand(0);
                    if (op1 instanceof PrimarySpiderDiagram) {
                        printMLAntecedent((PrimarySpiderDiagram) csd.getOperand(0), output);
                        exportDiagram(csd.getOperand(1), output);
                        return;
                    } else if (op1 instanceof NullSpiderDiagram) {
                        exportNullDiagram(printMLLeftBracket(output));
                        printMLRightBracket(output);
                        printMLImplication(output);
                        exportDiagram(csd.getOperand(1), output);
                        return;
                    }
                }
            }
            throw new ExportException(i18n("ERR_EXPORT_INVALID_SD_FOR_ML"));
        }

        private void printMLAntecedent(PrimarySpiderDiagram psd, Writer output) throws IOException {
            // Print the meta-universal quantifier part
            SortedSet<String> spiders = psd.getSpiders();
            if (psd.getSpidersCount() > 0) {
                Iterator<String> itr = spiders.iterator();
                printMLAll(output).append(itr.next());
                while (itr.hasNext()) {
                    output.append(' ').append(itr.next());
                }
                output.append(". ");
            }

            printMLLeftBracket(output);
            // Print the stuff within the meta-square brackets
            exportSpidersDistinct(psd, output, true);
            if (psd.getHabitatsCount() < 1 && psd.getShadedZonesCount() < 1) {
                printTrue(output);
            } else {
                exportHabitats(psd, output, true);
                exportShadedZones(psd, output, spiders);
            }
            printMLRightBracket(output);
            printMLImplication(output);
        }

        private void exportHabitat(String spider, Region region, Writer output) throws IOException {
            output.append(spider);
            printElementOf(output);
            exportRegion(region, output);
        }

        private void exportRegion(Region region, Writer output) throws IOException {
            SortedSet<Zone> zones = region.sortedZones();
            if (zones.isEmpty()) {
                printUniversalSet(output);
            } else {
                Iterator<Zone> itr = zones.iterator();
                Zone zone = itr.next();
                boolean needsParens = zone.getInContoursCount() > 1 || zone.getOutContoursCount() > 1 || (zone.getInContoursCount() == 1 && zone.getOutContoursCount() == 1);
                if (needsParens && zones.size() > 1) {
                    output.append('(');
                }
                exportZone(zone, output);
                if (needsParens && zones.size() > 1) {
                    output.append(')');
                }
                while (itr.hasNext()) {
                    zone = itr.next();
                    printUnion(output);
                    if (needsParens) {
                        output.append('(');
                    }
                    exportZone(zone, output);
                    if (needsParens) {
                        output.append(')');
                    }
//                    output.append(')');
                }
            }
        }

        private void exportZone(Zone zone, Writer output) throws IOException {
            SortedSet<String> inContours = zone.getInContours();
            SortedSet<String> outContours = zone.getOutContours();
            boolean someOuts = outContours != null && !outContours.isEmpty();
            boolean someIns = inContours != null && !inContours.isEmpty();
            if (someIns) {
                Iterator<String> itr = inContours.iterator();
                boolean needsParens = someOuts && inContours.size() > 1;
                if (needsParens) {
                    output.append('(');
                }
                output.append(itr.next());
                while (itr.hasNext()) {
                    printIntersection(output).append(itr.next());
                }
                if (needsParens) {
                    output.append(')');
                }
            }
            if (someOuts) {
                printSpaceIfSomethingInFront(output, someIns);
                output.append("-");
                printSpaceIfSomethingInFront(output, someIns);
                Iterator<String> itr = outContours.iterator();
                boolean needsParens = outContours.size() > 1;
                if (needsParens) {
                    output.append('(');
                }
                output.append(itr.next());
                while (itr.hasNext()) {
                    printUnion(output).append(itr.next());
                }
                if (needsParens) {
                    output.append(")");
                }
            }
        }

        private void printSpaceIfSomethingInFront(Writer output, boolean isSomethingInFront) throws IOException {
            if (isSomethingInFront) {
                output.append(" ");
            }
        }

        private class EqOperatorPrinter implements PrintCallback {

            @Override
            public void print(Writer output) throws IOException {
                printEquiv(output);
            }
        }

        private class OrOperatorPrinter implements PrintCallback {

            @Override
            public void print(Writer output) throws IOException {
                printOr(output);
            }
        }

        private class AndOperatorPrinter implements PrintCallback {

            @Override
            public void print(Writer output) throws IOException {
                printAnd(output);
            }
        }

        private class ImpOperatorPrinter implements PrintCallback {

            @Override
            public void print(Writer output) throws IOException {
                printImp(output);
            }
        }
    }

    private static final class ParameterDescriptions {

        public static final TreeMap<String, String> Parameters;

        static {
            Parameters = new TreeMap<>();
            Parameters.put(Parameter_UseXSymbols, "ISABELE_EXPORT_PAR_USE_X_SYMBOLS_DESCRIPTION");
            Parameters.put(Parameter_ML, "ISABELE_EXPORT_PAR_ML_DESCRIPTION");
        }
    }
}
