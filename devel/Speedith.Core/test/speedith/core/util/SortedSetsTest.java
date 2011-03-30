/*
 *   Project: Speedith.Core
 * 
 * File name: SortedSetsTest.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2010 Matej Urbas
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

import java.util.Comparator;
import java.util.SortedSet;
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
public class SortedSetsTest {

    public SortedSetsTest() {
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
     * Test of compare method, of class SortedSets.
     */
    @Test
    public void testCompare() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        SortedSet<String> s2 = null;
        int expResult = 0;
        int result = SortedSets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class SortedSets.
     */
    @Test
    public void testCompare7() {
        SortedSet<String> s1 = new TreeSet<String>(MyStringComparator.Instance);
        SortedSet<String> s2 = null;
        int expResult = 0;
        int result = SortedSets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class SortedSets.
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
        int result = SortedSets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class SortedSets.
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
        int result = SortedSets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class SortedSets.
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
        int result = SortedSets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class SortedSets.
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
        int result = SortedSets.compare(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compare method, of class SortedSets.
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
        int result = SortedSets.compare(s1, s2);
        assertEquals(expResult, result);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Test for 'compareNaturally'">
    /**
     * Test of compareNaturally method, of class SortedSets.
     */
    @Test
    public void testCompareNaturally() {
        SortedSet<String> s1 = new TreeSet<String>();
        SortedSet<String> s2 = null;
        int expResult = 0;
        int result = SortedSets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class SortedSets.
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
        int result = SortedSets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class SortedSets.
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
        int result = SortedSets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class SortedSets.
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
        int result = SortedSets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class SortedSets.
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
        int result = SortedSets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }

    /**
     * Test of compareNaturally method, of class SortedSets.
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
        int result = SortedSets.compareNaturally(s1, s2);
        assertEquals(expResult, result);
    }
    // </editor-fold>

}