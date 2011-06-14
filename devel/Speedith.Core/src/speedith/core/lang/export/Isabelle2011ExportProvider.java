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

import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import java.io.IOException;
import java.io.Writer;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Locale;
import java.util.Map;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.NullSpiderDiagram;
import speedith.core.lang.PrimarySpiderDiagram;
import static speedith.core.i18n.Translations.i18n;
import speedith.core.lang.Operator;
import static speedith.core.lang.Operator.*;
import speedith.core.lang.Region;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.Zone;
import speedith.core.util.Sets;

/**
 * The provider for exporting spider diagrams to Isabelle 2011 formulae.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class Isabelle2011ExportProvider extends SDExportProvider {

    /**
     * The name of the export format of this provider.
     */
    public static final String FormatName = "Isabelle2011";
    public static final String Parameter_UseXSymbols = "useXSymbols";

    @Override
    public String getFormatName() {
        return FormatName;
    }

    @Override
    public SDExporter getExporter(Map<String, String> parameters) {
        boolean useXSymbols = "true".equalsIgnoreCase(parameters == null ? null : parameters.get(Parameter_UseXSymbols));
        return new Exporter(useXSymbols);
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

    /**
     * The actual exporter class. This class does the actual translation from
     * spider diagrams to Isabelle's formulas.
     */
    private static class Exporter extends SDExporter {

        // TODO: Maybe I should write a generic pretty
        // printer, which takes into account precedence order of operators in
        // Isabelle automatically?
        // <editor-fold defaultstate="collapsed" desc="Fields">
        public static final String ISA_SYM_EX = "EX";
        public static final String ISA_XSYM_EXISTS = "∃";
        private boolean useXSymbols;
        // </editor-fold>

        // <editor-fold defaultstate="collapsed" desc="Constructors">
        public Exporter() {
            this(false);
        }

        public Exporter(boolean useXSymbols) {
            this.useXSymbols = useXSymbols;
        }
        // </editor-fold>

        // <editor-fold defaultstate="collapsed" desc="Isabelle Symbol/Operator Print Methods">
        private Writer printAnd(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<and>").append(' ');
//                return output.append(' ').append("∧").append(' ');
            } else {
                return output.append(' ').append("&").append(' ');
            }
        }

        private Writer printOr(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<or>").append(' ');
//                return output.append(' ').append("∨").append(' ');
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
//                return output.append(' ').append("∈").append(' ');
            } else {
                return output.append(' ').append(":").append(' ');
            }
        }

        private Writer printUnion(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<union>").append(' ');
//                return output.append(' ').append("∪").append(' ');
            } else {
                return output.append(' ').append("Un").append(' ');
            }
        }

        private Writer printIntersection(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<inter>").append(' ');
//                return output.append(' ').append("∩").append(' ');
            } else {
                return output.append(' ').append("Int").append(' ');
            }
        }

        private Writer printSubsetEq(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<subseteq>").append(' ');
//                return output.append(' ').append("⊆").append(' ');
            } else {
                return output.append(' ').append("<=").append(' ');
            }
        }

        private Writer printImp(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<longrightarrow>").append(' ');
//                return output.append(' ').append("⟶").append(' ');
            } else {
                return output.append(' ').append("-->").append(' ');
            }
        }

        private Writer printEquiv(Writer output) throws IOException {
            if (useXSymbols) {
                return output.append(' ').append("\\<longleftrightarrow>").append(' ');
//                return output.append(' ').append("⟷").append(' ');
            } else {
                return output.append(' ').append("<-->").append(' ');
            }
        }

        private Writer printTrue(Writer output) throws IOException {
            return output.append("True");
        }

        private Writer printExists(Writer output) throws IOException {
            if (useXSymbols) {
//                return output.append(ISA_XSYM_EXISTS);
                return output.append("\\<exists>");
            } else {
                return output.append(ISA_SYM_EX).append(' ');
            }
        }

        private Writer printUniversalSet(Writer output) throws IOException {
            return output.append("UNIV");
        }
        // </editor-fold>

        // <editor-fold defaultstate="collapsed" desc="Export Methods">
        @Override
        public void exportTo(SpiderDiagram sd, Writer output) throws IOException {
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
                throw new RuntimeException(i18n("ERR_ISAEXPORT_ARG_COUNT_INVALID", nsd.getOperandCount()));
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
            if (op.equals(OP_NAME_IMP)) {
                exportInfixOperator(nsd, output, new ImpOperatorPrinter());
            } else if (op.equals(OP_NAME_AND)) {
                exportInfixOperator(nsd, output, new AndOperatorPrinter());
            } else if (op.equals(OP_NAME_OR)) {
                exportInfixOperator(nsd, output, new OrOperatorPrinter());
            } else if (op.equals(OP_NAME_EQ)) {
                exportInfixOperator(nsd, output, new EqOperatorPrinter());
            }
        }

        private void exportPrimaryDiagram(PrimarySpiderDiagram psd, Writer output) throws IOException {
            output.append('(');
            SortedSet<String> spiders = psd.getSpiders();
            if (psd.getSpidersCount() > 0) {
                Iterator<String> itr = spiders.iterator();
                printExists(output).append(itr.next());
                while (itr.hasNext()) {
                    output.append(' ').append(itr.next());
                }
                output.append(". ");
            }
            exportSpidersDistinct(psd, output);
            if (psd.getHabitatsCount() < 1 && psd.getShadedZonesCount() < 1) {
                printTrue(output);
            } else {
                exportHabitats(psd, output);
                exportShadedZones(psd, output, spiders);
            }
            output.append(')');
        }

        private void exportShadedZones(PrimarySpiderDiagram psd, Writer output, SortedSet<String> spiders) throws IOException {
            if (psd.getShadedZonesCount() > 0) {
                SortedSet<Zone> shadedZones = psd.getShadedZones();
                Iterator<Zone> itr = shadedZones.iterator();
                Zone zone = itr.next();
                exportZone(zone, output);
                printSubsetEq(output);
                Sets.printSet(spiders, output);
            }
        }

        private void exportHabitats(PrimarySpiderDiagram psd, Writer output) throws IOException {
            if (psd.getHabitatsCount() > 0) {
                SortedMap<String, Region> habitats = psd.getHabitats();
                Iterator<String> itr = habitats.keySet().iterator();
                String spider = itr.next();
                exportHabitat(spider, habitats.get(spider), output);
                while (itr.hasNext()) {
                    spider = itr.next();
                    printAnd(output);
                    exportHabitat(spider, habitats.get(spider), output);
                }
                if (psd.getShadedZonesCount() > 0) {
                    printAnd(output);
                }
            }
        }

        private void exportSpidersDistinct(PrimarySpiderDiagram psd, Writer output) throws IOException {
            if (psd.getSpidersCount() > 1) {
                output.append("distinct");
                Sets.print(psd.getSpiders(), output, "[", "]", ", ");
                printAnd(output);
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

        private void exportHabitat(String spider, Region region, Writer output) throws IOException {
            output.append(spider);
            printElementOf(output);
            exportRegion(region, output);
        }

        private void exportRegion(Region region, Writer output) throws IOException {
            SortedSet<Zone> zones = region.getZones();
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
                if (someOuts) {
                    output.append(" - ");
                }
            }
            if (someOuts) {
                Iterator<String> itr = outContours.iterator();
                boolean needsParens = someIns && outContours.size() > 1;
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
        // </editor-fold>

        // <editor-fold defaultstate="collapsed" desc="Helper Classes">
        private class EqOperatorPrinter implements PrintCallback {

            public void print(Writer output) throws IOException {
                printEquiv(output);
            }
        }

        private class OrOperatorPrinter implements PrintCallback {

            public void print(Writer output) throws IOException {
                printOr(output);
            }
        }

        private class AndOperatorPrinter implements PrintCallback {

            public void print(Writer output) throws IOException {
                printAnd(output);
            }
        }

        private class ImpOperatorPrinter implements PrintCallback {

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
            Parameters = new TreeMap<String, String>();
            Parameters.put(Parameter_UseXSymbols, "ISABELE_EXPORT_PAR_USE_X_SYMBOLS_DESCRIPTION");
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Callback Interfaces">
    private static interface PrintCallback {

        void print(Writer output) throws IOException;
    }
    // </editor-fold>

    public static void main(String[] args) throws ReadingException {
        HashMap<String, String> params = new HashMap<String, String>();
        params.put(Isabelle2011ExportProvider.Parameter_UseXSymbols, "true");
        SDExporter exporter = SDExporting.getExporter(Isabelle2011ExportProvider.FormatName, params);
        SpiderDiagram sd = SpiderDiagramsReader.readSpiderDiagram("BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }");
        String sdStr = exporter.export(sd);
        System.out.println(sdStr);
    }
}
