/*
 *   Project: Speedith.Core
 * 
 * File name: SpiderDiagrams.java
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
package speedith.core.lang;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.WeakHashMap;
import static speedith.core.i18n.Translations.*;

/**
 * This class provides spider diagram factory methods and other spider-diagram
 * specific utilities.
 * <p><span style="font-weight:bold">Note</span>: This class must be used when
 * constructing spider diagrams.</p>
 * <p>It maintains a pool of living spider diagrams and reuses same spider
 * diagrams instead of creating new ones (for faster equality comparison).</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SpiderDiagrams {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private static final WeakHashMap<SpiderDiagram, WeakReference<SpiderDiagram>> pool = new WeakHashMap<SpiderDiagram, WeakReference<SpiderDiagram>>();
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Disabled Constructors">
    private SpiderDiagrams() {
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Factory Methods">
    /**
     * Creates an instance of the {@link NullSpiderDiagram null spider diagram}.
     * <p>This method does not put the returned null spider diagram into the
     * pool. There is always just one instance of the null spider diagram
     * around.</p>
     * @return an instance of the {@link NullSpiderDiagram null spider diagram}.
     */
    public static NullSpiderDiagram createNullSD() {
        return NullSpiderDiagram.getInstance();
    }

    /**
     * <p>Creates a new primary spider diagram with the given parameters.</p>
     * @param spiders a set of spiders (their names) that appear in this
     * spider diagram.
     * @param habitats a key-value map of spiders and their corresponding
     * {@link Region habitats}.
     * @param shadedZones a set of shaded {@link Zone zones}. 
     * @return the primary spider diagram.
     */
    public static PrimarySpiderDiagram createPrimarySD(Collection<String> spiders, Map<String, Region> habitats, Collection<Zone> shadedZones) {
        if ((spiders == null || spiders instanceof TreeSet)
                && (habitats == null || habitats instanceof TreeMap)
                && (shadedZones == null || shadedZones instanceof TreeSet)) {
            return createPrimarySD(spiders == null ? null : (TreeSet<String>) spiders,
                    habitats == null ? null : (TreeMap<String, Region>) habitats,
                    shadedZones == null ? null : (TreeSet<Zone>) shadedZones,
                    true);
        } else {
            return __createPrimarySD(new PrimarySpiderDiagram(spiders, habitats, shadedZones), false, spiders, habitats, shadedZones);
        }
    }

    /**
     * <p>Creates a new primary spider diagram with the given parameters.</p>
     * <p><span style="font-weight:bold">Note</span>: this method does not make
     * a copy of the given collections if possible.</p>
     * <p><span style="font-weight:bold">Warning</span>: you should use this
     * method only if you are sure that you will never modify the given
     * collections (of spiders, habitats and shaded zones) again.</p>
     * @param spiders a set of spiders (their names) that appear in this
     * spider diagram.
     * @param habitats a key-value map of spiders and their corresponding
     * {@link Region habitats}.
     * @param shadedZones a set of shaded {@link Zone zones}. 
     * @return the primary spider diagram.
     */
    public static PrimarySpiderDiagram createPrimarySDNoCopy(Collection<String> spiders, Map<String, Region> habitats, Collection<Zone> shadedZones) {
        if ((spiders == null || spiders instanceof TreeSet)
                && (habitats == null || habitats instanceof TreeMap)
                && (shadedZones == null || shadedZones instanceof TreeSet)) {
            return createPrimarySD(spiders == null ? null : (TreeSet<String>) spiders,
                    habitats == null ? null : (TreeMap<String, Region>) habitats,
                    shadedZones == null ? null : (TreeSet<Zone>) shadedZones,
                    false);
        } else {
            return __createPrimarySD(new PrimarySpiderDiagram(spiders, habitats, shadedZones), false, spiders, habitats, shadedZones);
        }
    }

    /**
     * <p>Creates a new primary spider diagram with the given parameters.</p>
     * <p><span style="font-weight:bold">Note</span>: setting the {@code
     * copyCollections} flag to {@code false} makes this operation a bit faster,
     * as this method will not create a copy of the given collections. However,
     * you <span style="font-weight:bold">must not</span> change these
     * collections afterwards, or it will lead to unexpected behaviour.</p>
     * <p>Creates a primary spider diagram from the given collections of
     * spiders, habitats and shaded zones without making a copy of these
     * collections. Afterwards it checks whether the created spider diagram is
     * in the pool already. If it is, it returns the one which is in the pool
     * and finishes. If it is not, however, then it puts the newly created
     * spider diagram into the pool. <span style="font-weight:bold">Note</span>:
     * If the {@code copyCollections} flag is set then before putting the newly
     * created spider diagram into the pool it first creates a new primary
     * spider diagram that actually copies the collections and puts this one
     * into the pool instead.</p>
     * @param spiders a set of spiders (their names) that appear in this
     * spider diagram.
     * @param habitats a key-value map of spiders and their corresponding
     * {@link Region habitats}.
     * @param shadedZones a set of shaded {@link Zone zones}. 
     * @param copyCollections indicates whether a copy of the above collections
     * should be made to construct the new primary spider diagram.
     * @return the primary spider diagram.
     */
    static PrimarySpiderDiagram createPrimarySD(TreeSet<String> spiders, TreeMap<String, Region> habitats, TreeSet<Zone> shadedZones, boolean copyCollections) {
        return __createPrimarySD(new PrimarySpiderDiagram(spiders, habitats, shadedZones), copyCollections, spiders, habitats, shadedZones);
    }

    /**
     * <p>Creates a new compound spider diagram with the given parameters.</p>
     * @param operator the {@link CompoundSpiderDiagram#getOperator() n-ary
     * operator} that operates over {@link CompoundSpiderDiagram#getOperands()
     * operands} of this n-ary spider diagram.
     * @param operands the {@link CompoundSpiderDiagram#getOperands() operands}
     * to the {@link CompoundSpiderDiagram#getOperator() operator}.
     * @return the primary spider diagram.
     */
    public static CompoundSpiderDiagram createCompoundSD(String operator, Collection<SpiderDiagram> operands) {
        if (operands instanceof ArrayList) {
            return createCompoundSD(operator, (ArrayList<SpiderDiagram>) operands, true);
        } else {
            return __createCompoundSD(new CompoundSpiderDiagram(operator, operands), false, operator, operands);
        }
    }

    /**
     * <p>Creates a new compound spider diagram with the given parameters.</p>
     * @param operator the {@link CompoundSpiderDiagram#getOperator() n-ary
     * operator} that operates over {@link CompoundSpiderDiagram#getOperands()
     * operands} of this n-ary spider diagram.
     * @param operands the {@link CompoundSpiderDiagram#getOperands() operands}
     * to the {@link CompoundSpiderDiagram#getOperator() operator}.
     * @return the primary spider diagram.
     */
    public static CompoundSpiderDiagram createCompoundSD(Operator operator, SpiderDiagram... operands) {
        if (operands == null) {
            return __createCompoundSD(new CompoundSpiderDiagram(operator, null), true, operator.getName(), null);
        } else {
            ArrayList<SpiderDiagram> operandsTmp = new ArrayList<SpiderDiagram>(Arrays.asList(operands));
            return __createCompoundSD(new CompoundSpiderDiagram(operator, operandsTmp), false, operator.getName(), null);
        }
    }

    /**
     * <p>Creates a new compound spider diagram with the given parameters.</p>
     * <p><span style="font-weight:bold">Note</span>: setting the {@code
     * copyCollection} flag to {@code false} makes this operation a bit faster,
     * as this method will not create a copy of the given operands collection.
     * However, you <span style="font-weight:bold">must not</span> change this
     * collection afterwards, or it will lead to unexpected behaviour.</p>
     * <p>How it works? It creates a compound spider diagram from the given
     * operator and operands without making a copy of the operands. Afterwards
     * it checks whether the created spider diagram is in the pool already. If
     * it is, it returns the one which is in the pool and finishes. If it is
     * not, then it puts the newly created spider diagram into the pool.
     * <span style="font-weight:bold">Note</span>: If the {@code
     * copyCollections} flag is set then, before putting the newly
     * created spider diagram into the pool, it first creates a new compound
     * spider diagram that actually copies the operands collection and puts this
     * new instance into the pool instead.</p>
     * @param operator the {@link CompoundSpiderDiagram#getOperator() n-ary
     * operator} that operates over {@link CompoundSpiderDiagram#getOperands()
     * operands} of this n-ary spider diagram.
     * @param operands the {@link CompoundSpiderDiagram#getOperands() operands}
     * to the {@link CompoundSpiderDiagram#getOperator() operator}.
     * @param copyCollection indicates whether a copy of the above collection
     * of spider diagrams should be made to construct the new compound spider
     * diagram.
     * @return the compound spider diagram.
     */
    public static CompoundSpiderDiagram createCompoundSD(String operator, ArrayList<SpiderDiagram> operands, boolean copyCollection) {
        return __createCompoundSD(new CompoundSpiderDiagram(Operator.fromString(operator), operands), copyCollection, operator, operands);
    }

    /**
     * <p>Creates a new compound spider diagram with the given parameters.</p>
     * <p><span style="font-weight:bold">Note</span>: setting the {@code
     * copyCollection} flag to {@code false} makes this operation a bit faster,
     * as this method will not create a copy of the given operands collection.
     * However, you <span style="font-weight:bold">must not</span> change this
     * collection afterwards, or it will lead to unexpected behaviour.</p>
     * <p>How it works? It creates a compound spider diagram from the given
     * operator and operands without making a copy of the operands. Afterwards
     * it checks whether the created spider diagram is in the pool already. If
     * it is, it returns the one which is in the pool and finishes. If it is
     * not, then it puts the newly created spider diagram into the pool.
     * <span style="font-weight:bold">Note</span>: If the {@code
     * copyCollections} flag is set then, before putting the newly
     * created spider diagram into the pool, it first creates a new compound
     * spider diagram that actually copies the operands collection and puts this
     * new instance into the pool instead.</p>
     * @param operator the {@link CompoundSpiderDiagram#getOperator() n-ary
     * operator} that operates over {@link CompoundSpiderDiagram#getOperands()
     * operands} of this n-ary spider diagram.
     * @param operands the {@link CompoundSpiderDiagram#getOperands() operands}
     * to the {@link CompoundSpiderDiagram#getOperator() operator}.
     * @param copyCollection indicates whether a copy of the above collection
     * of spider diagrams should be made to construct the new compound spider
     * diagram.
     * @return the compound spider diagram.
     */
    public static CompoundSpiderDiagram createCompoundSD(Operator operator, ArrayList<SpiderDiagram> operands, boolean copyCollection) {
        return __createCompoundSD(new CompoundSpiderDiagram(operator, operands), copyCollection, copyCollection ? operator.getName() : null, operands);
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Private Helper Methods">
    private static PrimarySpiderDiagram __createPrimarySD(PrimarySpiderDiagram psd, boolean copyCollections, Collection<String> tSpiders, Map<String, Region> tHabitats, Collection<Zone> tShadedZones) throws RuntimeException {
        synchronized (pool) {
            SpiderDiagram exPsd = __getSDFromPool(psd);
            // Is the spider diagram already in the pool?
            if (exPsd == null) {
                // It is not. Then add this newly created one into the pool and
                // return it.
                if (copyCollections) {
                    psd = new PrimarySpiderDiagram(tSpiders, tHabitats, tShadedZones);
                }
                pool.put(psd, new WeakReference<SpiderDiagram>(psd));
                return psd;
            }
            assert (exPsd instanceof PrimarySpiderDiagram) : i18n("GERR_ILLEGAL_STATE_EXPLANATION", i18n("ERR_PRIMARY_SD_EQUALS_NON_PRIMARY_SD"));
            // The diagram is already in the pool. Just return it.
            assert (((PrimarySpiderDiagram) exPsd).equals(psd)) : i18n("GERR_ILLEGAL_STATE");
            assert (psd.equals(exPsd)) : i18n("GERR_ILLEGAL_STATE");
            // The spider diagram might have been removed already (just
            // after we fetched it from the pool and before the reference
            // was assigned to the local variable). So, add it again to the
            // pool.
            pool.put(exPsd, new WeakReference<SpiderDiagram>(exPsd));
            return (PrimarySpiderDiagram) exPsd;
        }
    }

    /**
     * 
     * @param csd
     * @param copyCollection
     * @param operator
     * @param operands specify this parameter only if you want to make a copy of
     * it, otherwise the {@code csd} spider diagram will simply be inserted into
     * the pool (without any changes, and only if an instance of the compound
     * spider diagram does not already exist in the pool).
     * @return 
     */
    private static CompoundSpiderDiagram __createCompoundSD(CompoundSpiderDiagram csd, boolean copyCollection, String operator, Collection<SpiderDiagram> operands) {
        synchronized (pool) {
            SpiderDiagram exCsd = __getSDFromPool(csd);
            // Is the spider diagram already in the pool?
            if (exCsd == null) {
                // It is not. Then add this newly created one into the pool and
                // return it.
                if (copyCollection) {
                    csd = new CompoundSpiderDiagram(operator, operands);
                }
                pool.put(csd, new WeakReference<SpiderDiagram>(csd));
                return csd;
            }
            // The diagram is already in the pool. Just return it.
            assert (exCsd instanceof CompoundSpiderDiagram) : i18n("GERR_ILLEGAL_STATE_EXPLANATION", i18n("ERR_COMPOUND_SD_EQUALS_NON_COMPOUND_SD"));
            assert (((CompoundSpiderDiagram) exCsd).equals(csd)) : i18n("GERR_ILLEGAL_STATE");
            assert (csd.equals(exCsd)) : i18n("GERR_ILLEGAL_STATE");
            // The spider diagram might have been removed already (just
            // after we fetched it from the pool and before the reference
            // was assigned to the local variable). So, add it again to the
            // pool.
            pool.put(exCsd, new WeakReference<SpiderDiagram>(exCsd));
            return (CompoundSpiderDiagram) exCsd;
        }
    }

    private static SpiderDiagram __getSDFromPool(SpiderDiagram psd) {
        WeakReference<SpiderDiagram> poolSD = pool.get(psd);
        return poolSD == null ? null : poolSD.get();
    }
    //</editor-fold>
}
