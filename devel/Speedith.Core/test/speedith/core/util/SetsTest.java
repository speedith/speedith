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

import java.util.Map;
import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import static org.junit.Assert.*;

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

        public int compare(String o1, String o2) {
            return o1 == o2 ? 0 : (o1 == null ? o2.compareTo(o1) : -o1.compareTo(o2));
        }

    }

    /**
     * Test of compare method, of class Sets.
     */
    @Test
    public void testCompare() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
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
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
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
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
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
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
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
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
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
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
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
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
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
        SortedSet<String> s1 = new TreeSet<String>();
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
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>();
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
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>();
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
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>();
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
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<String>();
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
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<String>();
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
    public void test_equal_1() {
        Collection<String> s1 = new LinkedList<String>();
        s1.add("foo");
        s1.add("bar");
        s1.add("zar");
        Collection<String> s2 = new ArrayList<String>();
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
    public void test_equal_2() {
        Collection<String> s1 = null;
        Collection<String> s2 = new ArrayList<String>();
        boolean expResult = true;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void test_equal_3() {
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
    public void test_equal_4() {
        Collection<String> s1 = new TreeSet<String>();
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
    public void test_equal_5() {
        Collection<String> s1 = new LinkedList<String>();
        s1.add("foo");
        s1.add("bar");
        s1.add("bar");
        s1.add("zar");
        Collection<String> s2 = new ArrayList<String>();
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
    public void test_equal_6() {
        Collection<Integer> s1 = new LinkedList<Integer>();
        s1.add(1);
        s1.add(3);
        s1.add(3);
        s1.add(7);
        Collection<Double> s2 = new ArrayList<Double>();
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
    public void test_equal_7() {
        Collection<Integer> s1 = new LinkedList<Integer>();
        s1.add(1);
        s1.add(3);
        s1.add(3);
        s1.add(7);
        Collection<Short> s2 = new ArrayList<Short>();
        s2.add((short)1);
        s2.add((short)3);
        s2.add((short)3);
        s2.add((short)7);
        boolean expResult = false;
        boolean result = Sets.equal(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of the {@link Sets#equal(java.util.Collection, java.util.Collection)}
     * method.
     */
    @Test
    public void test_equal_8() {
        Collection<Integer> s1 = new ArrayList<Integer>();
        s1.add(1);
        s1.add(3);
        s1.add(3);
        s1.add(7);
        List<Integer> s2 = new ArrayList<Integer>();
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
    public void test_equal_9() {
        Collection<String> s1 = new TreeSet<String>();
        s1.add("foo");
        s1.add("zar");
        s1.add("bar");
        Set<String> s2 = new TreeSet<String>();
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
    public void test_equal_10() {
        Collection<String> s1 = new TreeSet<String>();
        s1.add("foo");
        s1.add("zar");
        s1.add("bar");
        Set<String> s2 = new TreeSet<String>();
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
    public void test_equal_11() {
        Collection<String> s1 = new TreeSet<String>();
        s1.add("foo");
        s1.add("zar");
        s1.add("bar");
        Set<String> s2 = new HashSet<String>();
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
    public void test_equal_12() {
        HashMap<String, Integer> s1 = new HashMap<String, Integer>();
        s1.put("foo", 2);
        s1.put("kre", 8);
        s1.put("zar", 1);
        s1.put("bar", 5);
        TreeMap<String, Integer> s2 = new TreeMap<String, Integer>();
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
    public void test_equal_13() {
        Map<String, Integer> s1 = new HashMap<String, Integer>();
        s1.put("foo", 2);
        s1.put("kre", 8);
        s1.put("zar", 1);
        s1.put("bar", 5);
        Map<String, Integer> s2 = new TreeMap<String, Integer>();
        s2.put("foo", 2);
        s2.put("bar", 5);
        s2.put("zar", 1);
        s2.put("kre", 8);
        boolean expResult = true;
        boolean result = Sets.equal(s1.entrySet(), s2.entrySet());
        assertEquals(expResult, result);
    }
    // </editor-fold>
    
    // <editor-fold defaultstate="collapsed" desc="isDifferenceEmpty Tests">
    /**
     * Test of isDifferenceEmpty method, of class Sets.
     */
    @Test
    public void test_isDifferenceEmpty1() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
        s2.add("a");
        s2.add("b");
        boolean expResult = false;
        boolean result = Sets.isDifferenceEmpty(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmpty method, of class Sets.
     */
    @Test
    public void test_isDifferenceEmpty2() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
        s2.add("d");
        s2.add("a");
        s2.add("b");
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmpty(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmpty method, of class Sets.
     */
    @Test
    public void test_isDifferenceEmpty3() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        SortedSet<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmpty(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmpty method, of class Sets.
     */
    @Test
    public void test_isDifferenceEmpty4() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmpty(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmpty method, of class Sets.
     */
    @Test
    public void test_isDifferenceEmpty5() {
        SortedSet<String> s1 = null;
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmpty(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmpty method, of class Sets.
     */
    @Test
    public void test_isDifferenceEmpty6() {
        SortedSet<String> s1 = null;
        SortedSet<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmpty(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmpty method, of class Sets.
     */
    @Test
    public void test_isDifferenceEmpty7() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
        s2.add("d");
        s2.add("a");
        s2.add("b");
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmpty(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmpty method, of class Sets.
     */
    @Test
    public void test_isDifferenceEmpty8() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        s1.add("c");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>(MyStringComparator.Instance);
        s2.add("b");
        s2.add("a");
        boolean expResult = false;
        boolean result = Sets.isDifferenceEmpty(s1, s2);
        assertEquals(expResult, result);
    }
    /**
     * Test of isDifferenceEmptyN method, of class Sets.
     */
    @Test
    public void test_isNaturalDifferenceEmpty1() {
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<String>();
        s2.add("a");
        s2.add("b");
        boolean expResult = false;
        boolean result = Sets.isDifferenceEmptyN(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmptyN method, of class Sets.
     */
    @Test
    public void test_isNaturalDifferenceEmpty2() {
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("a");
        s1.add("b");
        s1.add("d");
        SortedSet<String> s2 = new TreeSet<String>();
        s2.add("d");
        s2.add("a");
        s2.add("b");
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmptyN(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmptyN method, of class Sets.
     */
    @Test
    public void test_isNaturalDifferenceEmpty3() {
        SortedSet<String> s1 = new TreeSet<String>();
        SortedSet<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmptyN(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmptyN method, of class Sets.
     */
    @Test
    public void test_isNaturalDifferenceEmpty4() {
        SortedSet<String> s1 = new TreeSet<String>();
        SortedSet<String> s2 = new TreeSet<String>();
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmptyN(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmptyN method, of class Sets.
     */
    @Test
    public void test_isNaturalDifferenceEmpty5() {
        SortedSet<String> s1 = null;
        SortedSet<String> s2 = new TreeSet<String>();
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmptyN(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmptyN method, of class Sets.
     */
    @Test
    public void test_isNaturalDifferenceEmpty6() {
        SortedSet<String> s1 = null;
        SortedSet<String> s2 = null;
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmptyN(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmptyN method, of class Sets.
     */
    @Test
    public void test_isNaturalDifferenceEmpty7() {
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("a");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>();
        s2.add("d");
        s2.add("a");
        s2.add("b");
        boolean expResult = true;
        boolean result = Sets.isDifferenceEmptyN(s1, s2);
        assertEquals(expResult, result);
    }
    
    /**
     * Test of isDifferenceEmptyN method, of class Sets.
     */
    @Test
    public void test_isNaturalDifferenceEmpty8() {
        SortedSet<String> s1 = new TreeSet<String>();
        s1.add("c");
        s1.add("b");
        SortedSet<String> s2 = new TreeSet<String>();
        s2.add("b");
        s2.add("a");
        boolean expResult = false;
        boolean result = Sets.isDifferenceEmptyN(s1, s2);
        assertEquals(expResult, result);
    }
    // </editor-fold>

}