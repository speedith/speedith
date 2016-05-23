/*
 *   Project: Speedith.Core
 * 
 * File name: ZoneTest.java
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

import org.junit.*;

import java.util.*;

import static org.hamcrest.Matchers.hasSize;
import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ZoneTest {

    static LinkedList<String> m_inContours1;
    static ArrayList<String> m_outContours1;
    static Zone m_zone1;
    static Collection<String> m_inContours2;
    static Collection<String> m_outContours2;
    static Zone m_zone2;
    static TreeSet<String> m_inContours3;
    static TreeSet<String> m_outContours3;
    static Zone m_zone3;
    static TreeSet<String> m_inContours4;
    static TreeSet<String> m_outContours4;
    static Zone m_zone4;
    static TreeSet<String> m_inContours5;
    static TreeSet<String> m_outContours5;
    static Zone m_zone5;
    static TreeSet<String> m_outContours6;
    static Zone m_zone6;
    static TreeSet<String> m_inContours7;
    static Zone m_zone7;
    static Zone m_zone8;
    static Zone m_zone9;
    static Zone m_zone10;
    static Zone m_zone11;
    static Zone m_zone12;
    static Zone m_zone13;

    public ZoneTest() {
    }

    @BeforeClass
    public static void setUpClass() throws Exception {
    }

    static {
        // 1
        m_inContours1 = new LinkedList<>();
        m_inContours1.add("A");
        m_inContours1.add("C");
        m_inContours1.add("C");
        m_inContours1.add("U");
        m_inContours1.add("foo");
        m_inContours1.add("foo");
        m_outContours1 = new ArrayList<>();
        m_outContours1.add("B");
        m_outContours1.add("F");
        m_outContours1.add("F");
        m_outContours1.add("bar");
        m_outContours1.add("bar");
        m_outContours1.add("bar");
        m_zone1 = new Zone(m_inContours1, m_outContours1);

        m_inContours2 = new TreeSet<>();
        m_inContours2.add("A");
        m_inContours2.add("C");
        m_inContours2.add("U");
        m_inContours2.add("foo");
        m_outContours2 = new HashSet<>();
        m_outContours2.add("B");
        m_outContours2.add("F");
        m_outContours2.add("bar");
        m_zone2 = new Zone(m_inContours2, m_outContours2);

        m_inContours4 = new TreeSet<>();
        m_inContours4.add("A");
        m_inContours4.add("C");
        m_inContours4.add("U");
        m_inContours4.add("foo");
        m_outContours4 = new TreeSet<>();
        m_outContours4.add("B");
        m_outContours4.add("F");
        m_outContours4.add("bar");
        m_zone4 = new Zone(m_inContours4, m_outContours4);

        // 2
        m_inContours3 = new TreeSet<>();
        m_inContours3.add("A");
        m_inContours3.add("B");
        m_outContours3 = new TreeSet<>();
        m_outContours3.add("C");
        m_outContours3.add("D");
        m_outContours3.add("E");
        m_outContours3.add("F");
        m_zone3 = new Zone(m_inContours3, m_outContours3);

        // 3
        m_inContours5 = new TreeSet<>();
        m_inContours5.add("01s");
        m_inContours5.add("dsaknj");
        m_inContours5.add("dsanksaj");
        m_inContours5.add("otj332_");
        m_inContours5.add("_sadsakjn dsasa");
        m_outContours5 = new TreeSet<>();
        m_outContours5.add("po3nns");
        m_outContours5.add("sdfajkdni3329");
        m_outContours5.add("oifned32903");
        m_zone5 = new Zone(m_inContours5, m_outContours5);

        // 4
        m_outContours6 = new TreeSet<>();
        m_outContours6.add("po3nns");
        m_outContours6.add("sdfajkdni3329");
        m_outContours6.add("oifned32903");
        m_zone6 = new Zone(null, m_outContours6);

        // 5
        m_inContours7 = new TreeSet<>();
        m_inContours7.add("01s");
        m_inContours7.add("dsaknj");
        m_inContours7.add("dsanksaj");
        m_inContours7.add("otj332_");
        m_inContours7.add("_sadsakjn dsasa");
        m_zone7 = new Zone(m_inContours7, null);
        
        // 6
        m_zone8 = new Zone(null, null);
        m_zone9 = new Zone((TreeSet<String>)null, (TreeSet<String>)null);
        m_zone10 = new Zone((Collection<String>)null, (Collection<String>)null);
        
        m_zone11 = new Zone(new ArrayList<String>(), new TreeSet<String>());
        m_zone12 = new Zone(new TreeSet<String>(), new TreeSet<String>());
        
        m_zone13 = new Zone(Arrays.asList("A", "C", "E"), Arrays.asList("B", "C", "D"));
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

    /**
     * Test of getInContours method, of class Zone.
     */
    @Test
    public void testGetInContours() {
        assertEquals(m_zone1.getInContours(), m_inContours2);
        assertEquals(m_zone2.getInContours(), m_inContours2);
        assertEquals(m_zone3.getInContours(), m_inContours3);
        assertEquals(m_zone4.getInContours(), m_inContours4);
        assertEquals(m_zone2.getInContours(), m_inContours4);
        assertEquals(m_zone1.getInContours(), m_inContours4);
        assertEquals(m_zone5.getInContours(), m_inContours5);
        assertThat(m_zone6.getInContours(), hasSize(0));
        assertEquals(m_zone7.getInContours(), m_inContours7);
        assertThat(m_zone8.getInContours(), hasSize(0));
        assertThat(m_zone9.getInContours(), hasSize(0));
        assertThat(m_zone10.getInContours(), hasSize(0));
        assertThat(m_zone11.getInContours(), hasSize(0));
        assertThat(m_zone12.getInContours(), hasSize(0));
    }

    /**
     * Test of getInContoursCount method, of class Zone.
     */
    @Test
    public void testGetInContoursCount() {
        assertEquals(m_zone1.getInContoursCount(), m_inContours2.size());
        assertEquals(m_zone2.getInContoursCount(), m_inContours2.size());
        assertEquals(m_zone3.getInContoursCount(), m_inContours3.size());
        assertEquals(m_zone4.getInContoursCount(), m_inContours4.size());
        assertEquals(m_zone2.getInContoursCount(), m_inContours4.size());
        assertEquals(m_zone1.getInContoursCount(), m_inContours4.size());
        assertEquals(m_zone6.getInContoursCount(), 0);
        assertEquals(m_zone7.getInContoursCount(), m_inContours7.size());
        assertEquals(m_zone8.getInContoursCount(), 0);
        assertEquals(m_zone9.getInContoursCount(), 0);
        assertEquals(m_zone10.getInContoursCount(), 0);
        assertEquals(m_zone11.getInContoursCount(), 0);
        assertEquals(m_zone12.getInContoursCount(), 0);
    }

    /**
     * Test of getOutContours method, of class Zone.
     */
    @Test
    public void testGetOutContours() {
        assertEquals(m_zone1.getOutContours(), m_outContours2);
        assertEquals(m_zone2.getOutContours(), m_outContours2);
        assertEquals(m_zone3.getOutContours(), m_outContours3);
        assertEquals(m_zone4.getOutContours(), m_outContours4);
        assertEquals(m_zone2.getOutContours(), m_outContours4);
        assertEquals(m_zone1.getOutContours(), m_outContours4);
        assertEquals(m_zone6.getOutContours(), m_outContours6);
        assertThat(m_zone7.getOutContours(), hasSize(0));
        assertThat(m_zone8.getOutContours(), hasSize(0));
        assertThat(m_zone9.getOutContours(), hasSize(0));
        assertThat(m_zone10.getOutContours(), hasSize(0));
        assertThat(m_zone11.getOutContours(), hasSize(0));
        assertThat(m_zone12.getOutContours(), hasSize(0));
    }

    /**
     * Test of getOutContoursCount method, of class Zone.
     */
    @Test
    public void testGetOutContoursCount() {
        assertEquals(m_zone1.getOutContoursCount(), m_outContours2.size());
        assertEquals(m_zone2.getOutContoursCount(), m_outContours2.size());
        assertEquals(m_zone3.getOutContoursCount(), m_outContours3.size());
        assertEquals(m_zone4.getOutContoursCount(), m_outContours4.size());
        assertEquals(m_zone2.getOutContoursCount(), m_outContours4.size());
        assertEquals(m_zone1.getOutContoursCount(), m_outContours4.size());
        assertEquals(m_zone6.getOutContoursCount(), m_outContours6.size());
        assertEquals(m_zone7.getOutContoursCount(), 0);
        assertEquals(m_zone8.getOutContoursCount(), 0);
        assertEquals(m_zone9.getOutContoursCount(), 0);
        assertEquals(m_zone10.getOutContoursCount(), 0);
        assertEquals(m_zone11.getOutContoursCount(), 0);
        assertEquals(m_zone12.getOutContoursCount(), 0);
    }

    /**
     * Test of compareTo method, of class Zone.
     */
    @Test
    public void testCompareTo() {
        assertEquals(m_zone1.compareTo(m_zone2), 0);
        assertEquals(m_zone2.compareTo(m_zone1), 0);
        assertEquals(m_zone2.compareTo(m_zone4), 0);
        assertEquals(m_zone4.compareTo(m_zone2), 0);
        assertEquals(m_zone1.compareTo(m_zone4), 0);
        assertEquals(m_zone4.compareTo(m_zone1), 0);
        assertEquals(m_zone1.compareTo(m_zone3), 1);
        assertEquals(m_zone3.compareTo(m_zone1), -1);
        assertEquals(m_zone2.compareTo(m_zone3), 1);
        assertEquals(m_zone3.compareTo(m_zone2), -1);
        assertEquals(m_zone4.compareTo(m_zone3), 1);
        assertEquals(m_zone3.compareTo(m_zone4), -1);
        assertEquals(m_zone1.compareTo(m_zone1), 0);
        assertEquals(m_zone2.compareTo(m_zone2), 0);
        assertEquals(m_zone3.compareTo(m_zone3), 0);
        assertEquals(m_zone4.compareTo(m_zone4), 0);
        assertEquals(m_zone1.compareTo(m_zone6), 1);
        assertEquals(m_zone5.compareTo(m_zone1), -1);
        assertEquals(m_zone5.compareTo(m_zone3), -1);
        assertEquals(m_zone5.compareTo(m_zone5), 0);
        assertEquals(m_zone5.compareTo(m_zone6), 1);
        assertEquals(m_zone5.compareTo(m_zone7), 1);
        assertEquals(m_zone5.compareTo(m_zone8), 1);
        assertEquals(m_zone5.compareTo(m_zone9), 1);
        assertEquals(m_zone5.compareTo(m_zone10), 1);
        assertEquals(m_zone6.compareTo(m_zone1), -1);
        assertEquals(m_zone6.compareTo(m_zone3), -1);
        assertEquals(m_zone6.compareTo(m_zone6), 0);
        assertEquals(m_zone6.compareTo(m_zone7), -1);
        assertEquals(m_zone6.compareTo(m_zone8), 1);
        assertEquals(m_zone6.compareTo(m_zone9), 1);
        assertEquals(m_zone6.compareTo(m_zone10), 1);
        assertEquals(m_zone7.compareTo(m_zone6), 1);
        assertEquals(m_zone7.compareTo(m_zone1), -1);
        assertEquals(m_zone7.compareTo(m_zone3), -1);
        assertEquals(m_zone7.compareTo(m_zone8), 1);
        assertEquals(m_zone7.compareTo(m_zone9), 1);
        assertEquals(m_zone7.compareTo(m_zone10), 1);
        assertEquals(m_zone8.compareTo(m_zone1), -1);
        assertEquals(m_zone8.compareTo(m_zone3), -1);
        assertEquals(m_zone8.compareTo(m_zone6), -1);
        assertEquals(m_zone8.compareTo(m_zone7), -1);
        assertEquals(m_zone8.compareTo(m_zone9), 0);
        assertEquals(m_zone8.compareTo(m_zone10), 0);
        assertEquals(m_zone8.compareTo(m_zone11), 0);
        assertEquals(m_zone8.compareTo(m_zone12), 0);
    }

    /**
     * Test of equals method, of class Zone.
     */
    @Test
    @SuppressWarnings({"IncompatibleEquals", "ObjectEqualsNull"})
    public void testEquals() {
        assertTrue(m_zone1.equals(m_zone2));
        assertTrue(m_zone2.equals(m_zone1));
        assertTrue(m_zone2.equals(m_zone4));
        assertTrue(m_zone4.equals(m_zone2));
        assertTrue(m_zone1.equals(m_zone4));
        assertTrue(m_zone4.equals(m_zone1));
        assertTrue(m_zone1.equals(m_zone1));
        assertTrue(m_zone2.equals(m_zone2));
        assertTrue(m_zone3.equals(m_zone3));
        assertTrue(m_zone4.equals(m_zone4));
        assertFalse(m_zone3.equals(m_zone1));
        assertFalse(m_zone2.equals(m_zone3));
        assertFalse(m_zone3.equals(m_zone2));
        assertFalse(m_zone4.equals(m_zone3));
        assertFalse(m_zone3.equals(m_zone4));
        assertFalse(m_zone1.equals(NullSpiderDiagram.getInstance()));
        assertFalse(m_zone2.equals(NullSpiderDiagram.getInstance()));
        assertFalse(m_zone3.equals(NullSpiderDiagram.getInstance()));
        assertFalse(m_zone4.equals(NullSpiderDiagram.getInstance()));
        assertFalse(m_zone1.equals(null));
        assertFalse(m_zone2.equals(null));
        assertFalse(m_zone3.equals(null));
        assertFalse(m_zone4.equals(null));
        assertFalse(m_zone3.equals(m_zone5));
        assertFalse(m_zone5.equals(m_zone1));
        assertFalse(m_zone5.equals(m_zone3));
        assertTrue(m_zone5.equals(m_zone5));
        assertFalse(m_zone5.equals(m_zone6));
        assertFalse(m_zone5.equals(m_zone7));
        assertFalse(m_zone5.equals(m_zone8));
        assertFalse(m_zone5.equals(m_zone9));
        assertFalse(m_zone5.equals(m_zone10));
        assertFalse(m_zone6.equals(m_zone1));
        assertFalse(m_zone6.equals(m_zone3));
        assertTrue(m_zone6.equals(m_zone6));
        assertFalse(m_zone6.equals(m_zone7));
        assertFalse(m_zone6.equals(m_zone8));
        assertFalse(m_zone6.equals(m_zone9));
        assertFalse(m_zone6.equals(m_zone10));
        assertFalse(m_zone7.equals(m_zone6));
        assertFalse(m_zone7.equals(m_zone1));
        assertFalse(m_zone7.equals(m_zone3));
        assertFalse(m_zone7.equals(m_zone8));
        assertFalse(m_zone7.equals(m_zone9));
        assertFalse(m_zone7.equals(m_zone10));
        assertFalse(m_zone8.equals(m_zone1));
        assertFalse(m_zone8.equals(m_zone3));
        assertFalse(m_zone8.equals(m_zone6));
        assertFalse(m_zone8.equals(m_zone7));
        assertTrue(m_zone8.equals(m_zone9));
        assertTrue(m_zone8.equals(m_zone10));
        assertTrue(m_zone8.equals(m_zone11));
        assertTrue(m_zone8.equals(m_zone12));
    }

    /**
     * Test of hashCode method, of class Zone.
     */
    @Test
    public void testHashCode() {
        assertEquals(m_zone1.hashCode(), m_zone2.hashCode());
        assertEquals(m_zone2.hashCode(), m_zone1.hashCode());
        assertEquals(m_zone2.hashCode(), m_zone4.hashCode());
        assertEquals(m_zone4.hashCode(), m_zone2.hashCode());
        assertEquals(m_zone1.hashCode(), m_zone4.hashCode());
        assertEquals(m_zone4.hashCode(), m_zone1.hashCode());
        assertEquals(m_zone1.hashCode(), m_zone1.hashCode());
        assertEquals(m_zone2.hashCode(), m_zone2.hashCode());
        assertEquals(m_zone3.hashCode(), m_zone3.hashCode());
        assertEquals(m_zone4.hashCode(), m_zone4.hashCode());
        assertEquals(m_zone8.hashCode(), m_zone9.hashCode());
        assertEquals(m_zone8.hashCode(), m_zone10.hashCode());
        assertEquals(m_zone8.hashCode(), m_zone11.hashCode());
        assertEquals(m_zone8.hashCode(), m_zone12.hashCode());
    }

    /**
     * Test of hashCode method, of class Zone.
     */
    @Test
    public void testHashMap() {
        HashSet<Zone> sds = new HashSet<>();
        sds.add(m_zone1);
        sds.add(m_zone2);
        sds.add(m_zone3);
        sds.add(m_zone4);
        sds.add(m_zone5);
        sds.add(m_zone6);
        sds.add(m_zone7);
        sds.add(m_zone8);
        sds.add(m_zone9);
        sds.add(m_zone10);
        sds.add(m_zone11);
        sds.add(m_zone12);
        assertEquals(6, sds.size());
        assertTrue(sds.contains(m_zone1));
        assertTrue(sds.contains(m_zone2));
        assertTrue(sds.contains(m_zone3));
        assertTrue(sds.contains(m_zone4));
        assertTrue(sds.contains(m_zone5));
        assertTrue(sds.contains(m_zone6));
        assertTrue(sds.contains(m_zone7));
        assertTrue(sds.contains(m_zone8));
        assertTrue(sds.contains(m_zone9));
        assertTrue(sds.contains(m_zone10));
        assertFalse(sds.contains(null));
        assertFalse(sds.contains(new Zone(Arrays.asList(new String[]{ "a" }), null)));
        assertTrue(sds.contains(new Zone(Arrays.asList(new String[]{ "B", "A" }), Arrays.asList(new String[]{ "E", "C", "F", "D" }))));
        assertTrue(sds.contains(new Zone(Arrays.asList(new String[]{ "B", "A", "A" }), Arrays.asList(new String[]{ "E", "C", "F", "F", "D" }))));
        assertFalse(sds.contains(new Zone(Arrays.asList(new String[]{ "B", "A", "A" }), null)));
        assertFalse(sds.contains(new Zone(null, Arrays.asList(new String[]{ "E", "C", "F", "F", "D" }))));
        assertFalse(sds.contains(new Zone(Arrays.asList(new String[]{ "B" }), Arrays.asList(new String[]{ "E", "C", "F", "F", "D" }))));
        assertFalse(sds.contains(new Zone(Arrays.asList(new String[]{ "B" }), null)));
        assertFalse(sds.contains(new Zone(null, Arrays.asList(new String[]{ "E", "C", "F", "F", "D" }))));
    }

    @Test
    public void testWithInContours() {
        Zone expResult = m_zone5;
        Zone result = m_zone6.withInContours(m_zone5.getInContours().toArray(new String[0]));
        assertEquals(expResult, result);
    }

    @Test
    public void testWithOutContours() {
        Zone expResult = m_zone5;
        Zone result = m_zone7.withOutContours(m_zone5.getOutContours().toArray(new String[0]));
        assertEquals(expResult, result);
    }

    @Test
    public void testFromInContours() {
        Zone expResult = m_zone6;
        Zone result = Zone.fromOutContours(m_zone5.getOutContours().toArray(new String[0]));
        assertEquals(expResult, result);
    }

    @Test
    public void testFromOutContours() {
        Zone expResult = m_zone7;
        Zone result = Zone.fromInContours(m_zone5.getInContours().toArray(new String[0]));
        assertEquals(expResult, result);
    }

    @Test
    public void testIsValid() {
        SortedSet<String> contours = new TreeSet<>(Arrays.asList("A", "B", "C", "D", "E", "F"));
        Zone instance = m_zone3;
        boolean expResult = true;
        boolean result = instance.isValid(contours);
        assertEquals(expResult, result);
    }

    @Test
    public void testIsValid2() {
        SortedSet<String> contours = new TreeSet<>(Arrays.asList("A", "B", "C", "D", "E"));
        Zone instance = m_zone3;
        boolean expResult = false;
        boolean result = instance.isValid(contours);
        assertEquals(expResult, result);
    }

    @Test
    public void testIsValid3() {
        SortedSet<String> contours = new TreeSet<>(Arrays.asList("A", "B", "C", "D", "E", "F", "G"));
        Zone instance = m_zone3;
        boolean expResult = false;
        boolean result = instance.isValid(contours);
        assertEquals(expResult, result);
    }

    @Test
    public void testIsValid4() {
        SortedSet<String> contours = new TreeSet<>(Arrays.asList("A", "B", "C", "D", "E"));
        Zone instance = m_zone13;
        boolean expResult = false;
        boolean result = instance.isValid(contours);
        assertEquals(expResult, result);
    }

    @Test
    public void getAllContours_should_return_the_union_of_in_and_out_contours() {
        Zone zone = Zone.fromInContours("Foo", "Bar").withOutContours("Zar");
        TreeSet<String> expectedContours = new TreeSet<>(Arrays.asList("Foo", "Bar", "Zar"));
        assertEquals(expectedContours, zone.getAllContours());
    }
}
