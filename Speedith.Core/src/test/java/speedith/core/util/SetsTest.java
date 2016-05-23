/*
 *   Project: Speedith.Core
 * 
 * File name: SetsTest.java
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
package speedith.core.util;

import org.junit.*;
import propity.util.Sets;

import java.util.*;

import static org.junit.Assert.assertEquals;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SetsTest {

    public SetsTest() {
    }

    @BeforeClass
    public static void setUpClass() throws Exception {
    }

    @AfterClass
    public static void tearDownClass() throws Exception {
    }

    @Before
    public void setUp() {
    }

    @After
    public void tearDown() {
    }

    // <editor-fold defaultstate="collapsed" desc="Tests for 'compare'">
    public static final class MyStringComparator implements
            Comparator<String> {

        private MyStringComparator() {
        }
        public static MyStringComparator Instance = new MyStringComparator();

        @Override
        public int compare(String o1, String o2) {
            return o1 == o2 ? 0 : (o1 == null ? o2.compareTo(o1) : -o1.compareTo(o2));
        }
    }

    /**
     * Test of compare method, of class Sets.
     */
    @Test
    public void testCompare() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        SortedSet<String> s2 = null;
        int expResult = 0;
        int result = Sets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class Sets.
     */
    @Test
    public void testCompare7() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        SortedSet<String> s2 = null;
        int expResult = 0;
        int result = Sets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class Sets.
     */
    @Test
    public void testCompare1() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("a");
        s2.add("b");
        int expResult = 0;
        int result = Sets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class Sets.
     */
    @Test
    public void testCompare2() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("a");
        s2.add("b");
        s2.add("b");
        int expResult = 0;
        int result = Sets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class Sets.
     */
    @Test
    public void testCompare3() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("a");
        s2.add("b");
        s2.add("c");
        int expResult = 1;
        int result = Sets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class Sets.
     */
    @Test
    public void testCompare4() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("a");
        s2.add("b");
        s2.add("c");
        int expResult = -1;
        int result = Sets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class Sets.
     */
    @Test
    public void testCompare5() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("a");
        s2.add("b");
        int expResult = -1;
        int result = Sets.compare(s1, s2);
        assertEquals(expResult, result);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Test for 'compareNaturally'">
    /**
     * Test of compareNaturally method, of class Sets.
     */
    @Test
    public void testCompareNaturally() {
        SortedSet<String> s1 = new TreeSet<>();
        SortedSet<String> s2 = null;
        int expResult = 0;
        int result = Sets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class Sets.
     */
    @Test
    public void testCompareNaturally1() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("a");
        s2.add("b");
        int expResult = 0;
        int result = Sets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class Sets.
     */
    @Test
    public void testCompareNaturally2() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("a");
        s2.add("b");
        s2.add("b");
        int expResult = 0;
        int result = Sets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class Sets.
     */
    @Test
    public void testCompareNaturally3() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("a");
        s2.add("b");
        s2.add("c");
        int expResult = -1;
        int result = Sets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class Sets.
     */
    @Test
    public void testCompareNaturally4() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("a");
        s2.add("b");
        s2.add("c");
        int expResult = 1;
        int result = Sets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class Sets.
     */
    @Test
    public void testCompareNaturally5() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("a");
        s2.add("b");
        int expResult = 1;
        int result = Sets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Tests for 'equal'">
    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual() {
        Collection<String> s1 = new LinkedList<>();
        s1.add("foo");
        s1.add("bar");
        s1.add("zar");
        Collection<String> s2 = new ArrayList<>();
        s2.add("foo");
        s2.add("bar");
        s2.add("zar");
        boolean expResult = true;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual2() {
        Collection<String> s1 = null;
        Collection<String> s2 = new ArrayList<>();
        boolean expResult = true;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual3() {
        Collection<String> s1 = null;
        Collection<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual4() {
        Collection<String> s1 = new TreeSet<>();
        Collection<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual5() {
        Collection<String> s1 = new LinkedList<>();
        s1.add("foo");
        s1.add("bar");
        s1.add("bar");
        s1.add("zar");
        Collection<String> s2 = new ArrayList<>();
        s2.add("foo");
        s2.add("bar");
        s2.add("zar");
        boolean expResult = false;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual6() {
        Collection<Integer> s1 = new LinkedList<>();
        s1.add(1);
        s1.add(3);
        s1.add(3);
        s1.add(7);
        Collection<Double> s2 = new ArrayList<>();
        s2.add(1.0);
        s2.add(3.0);
        s2.add(3.0);
        s2.add(7.0);
        boolean expResult = false;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual7() {
        Collection<Integer> s1 = new LinkedList<>();
        s1.add(1);
        s1.add(3);
        s1.add(3);
        s1.add(7);
        Collection<Short> s2 = new ArrayList<>();
        s2.add((short) 1);
        s2.add((short) 3);
        s2.add((short) 3);
        s2.add((short) 7);
        boolean expResult = false;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual8() {
        Collection<Integer> s1 = new ArrayList<>();
        s1.add(1);
        s1.add(3);
        s1.add(3);
        s1.add(7);
        List<Integer> s2 = new ArrayList<>();
        s2.add(1);
        s2.add(7);
        s2.add(1, 3);
        s2.add(1, 3);
        boolean expResult = true;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual9() {
        Collection<String> s1 = new TreeSet<>();
        s1.add("foo");
        s1.add("zar");
        s1.add("bar");
        Set<String> s2 = new TreeSet<>();
        s2.add("bar");
        s2.add("foo");
        s2.add("zar");
        boolean expResult = true;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual10() {
        Collection<String> s1 = new TreeSet<>();
        s1.add("foo");
        s1.add("zar");
        s1.add("bar");
        Set<String> s2 = new TreeSet<>();
        s2.add("bar");
        s2.add("fooo");
        s2.add("zar");
        boolean expResult = false;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual11() {
        Collection<String> s1 = new TreeSet<>();
        s1.add("foo");
        s1.add("zar");
        s1.add("bar");
        Set<String> s2 = new HashSet<>();
        s2.add("bar");
        s2.add("zar");
        s2.add("foo");
        boolean expResult = true;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual12() {
        HashMap<String, Integer> s1 = new HashMap<>();
        s1.put("foo", 2);
        s1.put("kre", 8);
        s1.put("zar", 1);
        s1.put("bar", 5);
        TreeMap<String, Integer> s2 = new TreeMap<>();
        s2.put("foo", 2);
        s2.put("bar", 5);
        s2.put("zar", 1);
        s2.put("kre", 8);
        s2.put("kre1", 8);
        boolean expResult = false;
        boolean result = Sets.equal(s1.entrySet(), s2.entrySet());
        assertEquals(expResult, result);
    }

    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void testEqual13() {
        Map<String, Integer> s1 = new HashMap<>();
        s1.put("foo", 2);
        s1.put("kre", 8);
        s1.put("zar", 1);
        s1.put("bar", 5);
        Map<String, Integer> s2 = new TreeMap<>();
        s2.put("foo", 2);
        s2.put("bar", 5);
        s2.put("zar", 1);
        s2.put("kre", 8);
        boolean expResult = true;
        boolean result = Sets.equal(s1.entrySet(), s2.entrySet());
        assertEquals(expResult, result);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="isSubset Tests">
    /**
     * Test of isSubset method, of class Sets.
     */
    @Test
    public void testIsSubset() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("a");
        s2.add("b");
        boolean expResult = false;
        boolean result = Sets.isSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isSubset method, of class Sets.
     */
    @Test
    public void testIsSubset2() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("d");
        s2.add("a");
        s2.add("b");
        boolean expResult = true;
        boolean result = Sets.isSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isSubset method, of class Sets.
     */
    @Test
    public void testIsSubset3() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        SortedSet<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.isSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isSubset method, of class Sets.
     */
    @Test
    public void testIsSubset4() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        boolean expResult = true;
        boolean result = Sets.isSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isSubset method, of class Sets.
     */
    @Test
    public void testIsSubset5() {
        SortedSet<String> s1 = null;
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        boolean expResult = true;
        boolean result = Sets.isSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isSubset method, of class Sets.
     */
    @Test
    public void testIsSubset6() {
        SortedSet<String> s1 = null;
        SortedSet<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.isSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isSubset method, of class Sets.
     */
    @Test
    public void testIsSubset7() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("d");
        s2.add("a");
        s2.add("b");
        boolean expResult = true;
        boolean result = Sets.isSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isSubset method, of class Sets.
     */
    @Test
    public void testIsSubset8() {
        SortedSet<String> s1 = new TreeSet<>(MyStringComparator.Instance);
        s1.add("c");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>(MyStringComparator.Instance);
        s2.add("b");
        s2.add("a");
        boolean expResult = false;
        boolean result = Sets.isSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isNaturalSubset method, of class Sets.
     */
    @Test
    public void testIsNaturalSubset() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("a");
        s2.add("b");
        boolean expResult = false;
        boolean result = Sets.isNaturalSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isNaturalSubset method, of class Sets.
     */
    @Test
    public void testIsNaturalSubset2() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("d");
        s2.add("a");
        s2.add("b");
        boolean expResult = true;
        boolean result = Sets.isNaturalSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isNaturalSubset method, of class Sets.
     */
    @Test
    public void testIsNaturalSubset3() {
        SortedSet<String> s1 = new TreeSet<>();
        SortedSet<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.isNaturalSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isNaturalSubset method, of class Sets.
     */
    @Test
    public void testIsNaturalSubset4() {
        SortedSet<String> s1 = new TreeSet<>();
        SortedSet<String> s2 = new TreeSet<>();
        boolean expResult = true;
        boolean result = Sets.isNaturalSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isNaturalSubset method, of class Sets.
     */
    @Test
    public void testIsNaturalSubset5() {
        SortedSet<String> s1 = null;
        SortedSet<String> s2 = new TreeSet<>();
        boolean expResult = true;
        boolean result = Sets.isNaturalSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isNaturalSubset method, of class Sets.
     */
    @Test
    public void testIsNaturalSubset6() {
        SortedSet<String> s1 = null;
        SortedSet<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.isNaturalSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isNaturalSubset method, of class Sets.
     */
    @Test
    public void testIsNaturalSubset7() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("d");
        s2.add("a");
        s2.add("b");
        boolean expResult = true;
        boolean result = Sets.isNaturalSubset(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of isNaturalSubset method, of class Sets.
     */
    @Test
    public void testIsNaturalSubset8() {
        SortedSet<String> s1 = new TreeSet<>();
        s1.add("c");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<>();
        s2.add("b");
        s2.add("a");
        boolean expResult = false;
        boolean result = Sets.isNaturalSubset(s1, s2);
        assertEquals(expResult, result);
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="'disjoint' Tests">
    @Test
    public void testDisjoint() {
        SortedSet<String> a = new TreeSet<>(MyStringComparator.Instance);
        a.add("a");
        a.add("b");
        SortedSet<String> b = new TreeSet<>(MyStringComparator.Instance);
        b.add("a");
        b.add("b");
        boolean expResult = false;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint2() {
        SortedSet<String> a = new TreeSet<>(MyStringComparator.Instance);
        a.add("d");
        a.add("e");
        SortedSet<String> b = new TreeSet<>(MyStringComparator.Instance);
        b.add("a");
        b.add("b");
        b.add("c");
        boolean expResult = true;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint3() {
        SortedSet<String> a = new TreeSet<>(MyStringComparator.Instance);
        a.add("a");
        a.add("b");
        SortedSet<String> b = new TreeSet<>(MyStringComparator.Instance);
        b.add("c");
        b.add("d");
        b.add("e");
        boolean expResult = true;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint4() {
        SortedSet<String> a = new TreeSet<>(MyStringComparator.Instance);
        SortedSet<String> b = new TreeSet<>(MyStringComparator.Instance);
        b.add("c");
        b.add("d");
        b.add("e");
        boolean expResult = true;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint5() {
        SortedSet<String> a = new TreeSet<>(MyStringComparator.Instance);
        SortedSet<String> b = new TreeSet<>(MyStringComparator.Instance);
        boolean expResult = true;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint6() {
        SortedSet<String> a = new TreeSet<>(MyStringComparator.Instance);
        a.add("a");
        a.add("b");
        SortedSet<String> b = new TreeSet<>(MyStringComparator.Instance);
        boolean expResult = true;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint7() {
        SortedSet<String> a = null;
        SortedSet<String> b = new TreeSet<>(MyStringComparator.Instance);
        b.add("e");
        boolean expResult = true;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint8() {
        SortedSet<String> a = new TreeSet<>(MyStringComparator.Instance);
        a.add("a");
        SortedSet<String> b = null;
        boolean expResult = true;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint9() {
        SortedSet<String> a = null;
        SortedSet<String> b = null;
        boolean expResult = true;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testDisjoint10() {
        SortedSet<String> a = new TreeSet<>(MyStringComparator.Instance);
        a.add("a");
        a.add("b");
        SortedSet<String> b = new TreeSet<>(MyStringComparator.Instance);
        b.add("c");
        b.add("b");
        b.add("e");
        boolean expResult = false;
        boolean result = Sets.disjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint() {
        SortedSet<String> a = new TreeSet<>();
        a.add("a");
        a.add("b");
        SortedSet<String> b = new TreeSet<>();
        b.add("a");
        b.add("b");
        boolean expResult = false;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint2() {
        SortedSet<String> a = new TreeSet<>();
        a.add("d");
        a.add("e");
        SortedSet<String> b = new TreeSet<>();
        b.add("a");
        b.add("b");
        b.add("c");
        boolean expResult = true;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint3() {
        SortedSet<String> a = new TreeSet<>();
        a.add("a");
        a.add("b");
        SortedSet<String> b = new TreeSet<>();
        b.add("c");
        b.add("d");
        b.add("e");
        boolean expResult = true;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint4() {
        SortedSet<String> a = new TreeSet<>();
        SortedSet<String> b = new TreeSet<>();
        b.add("c");
        b.add("d");
        b.add("e");
        boolean expResult = true;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint5() {
        SortedSet<String> a = new TreeSet<>();
        SortedSet<String> b = new TreeSet<>();
        boolean expResult = true;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint6() {
        SortedSet<String> a = new TreeSet<>();
        a.add("a");
        a.add("b");
        SortedSet<String> b = new TreeSet<>();
        boolean expResult = true;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint7() {
        SortedSet<String> a = null;
        SortedSet<String> b = new TreeSet<>();
        b.add("e");
        boolean expResult = true;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint8() {
        SortedSet<String> a = new TreeSet<>();
        a.add("a");
        SortedSet<String> b = null;
        boolean expResult = true;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint9() {
        SortedSet<String> a = null;
        SortedSet<String> b = null;
        boolean expResult = true;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint10() {
        SortedSet<String> a = new TreeSet<>();
        a.add("a");
        a.add("b");
        SortedSet<String> b = new TreeSet<>();
        b.add("c");
        b.add("b");
        b.add("e");
        boolean expResult = false;
        boolean result = Sets.naturallyDisjoint(a, b);
        assertEquals(expResult, result);
    }

    @Test
    public void testNaturallyDisjoint11() {
        Random rng = new Random();
        final int repCount = 100;
        boolean retVals[] = new boolean[repCount];
        for (int i = 0; i < repCount; i++) {
            SortedSet<Integer> a = randomSet(rng, 0, 10, rng.nextInt(10));
            SortedSet<Integer> b = randomSet(rng, 0, 10, rng.nextInt(10));
            boolean expResult = disjointImpl(a, b);
            boolean result = Sets.naturallyDisjoint(a, b);
            assertEquals(expResult, result);
            retVals[i] = result;
        }
    }

    public static TreeSet<Integer> randomSet(Random rng, int min, int max, int size) {
        TreeSet<Integer> treeSet = new TreeSet<>();
        if (rng == null) {
            rng = new Random();
        }
        for (int i = 0; i < size; i++) {
            treeSet.add(rng.nextInt(Math.abs(max - min) + 1) + min);
        }
        return treeSet;
    }

    public static <E> boolean disjointImpl(SortedSet<E> a, SortedSet<E> b) {
        if (a == null || b == null) {
            return true;
        } else {
            a = new TreeSet<>(a);
            a.retainAll(b);
            return a.isEmpty();
        }
    }
    //</editor-fold>
}