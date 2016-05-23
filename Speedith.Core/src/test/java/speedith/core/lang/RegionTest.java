/*
 *   Project: Speedith.Core
 * 
 * File name: RegionTest.java
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

import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class RegionTest {

    static List<Zone> m_zones1;
    static Region m_region1;
    static List<Zone> m_zones2;
    static Region m_region2;
    static TreeSet<Zone> m_zones3;
    static Region m_region3;
    static List<Zone> m_zones4;
    static Region m_region4;
    static Region m_region5;
    static Region m_region6;
    static Region m_region7;
    static List<Zone> m_zones8;
    static Region m_region8;
    static TreeSet<Zone> m_zones9;
    static Region m_region9;
    static TreeSet<Zone> m_zones10;
    static Region m_region10;
    static TreeSet<Zone> m_zones11;
    static Region m_region11;
    static List<Zone> m_zones12;
    static Region m_region12;

    public RegionTest() {
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

    static {
        // 1
        m_zones1 = Arrays.asList(new Zone[]{ZoneTest.m_zone1,
                    ZoneTest.m_zone2,
                    ZoneTest.m_zone3,
                    ZoneTest.m_zone4,
                    ZoneTest.m_zone5,
                    ZoneTest.m_zone6,
                    ZoneTest.m_zone7,
                    ZoneTest.m_zone8,
                    ZoneTest.m_zone9,
                    ZoneTest.m_zone10});
        m_region1 = new Region(m_zones1);
        m_zones2 = Arrays.asList(new Zone[]{ZoneTest.m_zone1,
                    ZoneTest.m_zone3,
                    ZoneTest.m_zone5,
                    ZoneTest.m_zone6,
                    ZoneTest.m_zone7,
                    ZoneTest.m_zone10});
        m_region2 = new Region(m_zones2);
        m_zones3 = new TreeSet<>(Arrays.asList(new Zone[]{ZoneTest.m_zone1,
                ZoneTest.m_zone3,
                ZoneTest.m_zone5,
                ZoneTest.m_zone6,
                ZoneTest.m_zone7,
                ZoneTest.m_zone10}));
        m_region3 = new Region(m_zones3);
        m_zones8 = Arrays.asList(new Zone[]{ZoneTest.m_zone1,
                    ZoneTest.m_zone2,
                    ZoneTest.m_zone3,
                    ZoneTest.m_zone3,
                    ZoneTest.m_zone3,
                    ZoneTest.m_zone4,
                    ZoneTest.m_zone5,
                    ZoneTest.m_zone5,
                    ZoneTest.m_zone6,
                    ZoneTest.m_zone6,
                    ZoneTest.m_zone6,
                    ZoneTest.m_zone7,
                    ZoneTest.m_zone8,
                    ZoneTest.m_zone8,
                    ZoneTest.m_zone8,
                    ZoneTest.m_zone9,
                    ZoneTest.m_zone9,
                    ZoneTest.m_zone10});
        m_region8 = new Region(m_zones8);
        
        // 2
        m_zones4 = Arrays.asList(new Zone[]{ZoneTest.m_zone1,
                    ZoneTest.m_zone5,
                    ZoneTest.m_zone6,
                    ZoneTest.m_zone10});
        m_region4 = new Region(m_zones4);

        // 3
        m_region5 = new Region((Collection<Zone>)null);
        m_region6 = new Region((TreeSet<Zone>)null);
        m_region7 = new Region((Collection<Zone>)null);
        m_zones11 = new TreeSet<>(Arrays.asList(new Zone[]{}));
        m_region11 = new Region(m_zones11);
        m_zones12 = Arrays.asList(new Zone[]{});
        m_region12 = new Region(m_zones12);
        
        // 4
        m_zones9 = new TreeSet<>(Arrays.asList(new Zone[]{ZoneTest.m_zone3,
                ZoneTest.m_zone5,
                ZoneTest.m_zone7}));
        m_region9 = new Region(m_zones9);
        
        // 5
        m_zones10 = new TreeSet<>(Arrays.asList(new Zone[]{ZoneTest.m_zone5}));
        m_region10 = new Region(m_zones10);
    }

    /**
     * Test of hashCode method, of class Region.
     */
    @Test
    public void testEquals() {
        assertTrue(m_region1.equals(m_region1)); // 1
        assertTrue(m_region1.equals(m_region2));
        assertTrue(m_region1.equals(m_region3));
        assertFalse(m_region1.equals(m_region4));
        assertFalse(m_region1.equals(m_region5));
        assertFalse(m_region1.equals(m_region6));
        assertFalse(m_region1.equals(m_region7));
        assertTrue(m_region1.equals(m_region8));
        assertFalse(m_region1.equals(m_region9));
        assertFalse(m_region1.equals(m_region10));
        assertFalse(m_region1.equals(m_region11));
        assertFalse(m_region1.equals(m_region12));
        
        assertTrue(m_region2.equals(m_region1));
        assertTrue(m_region2.equals(m_region2));
        assertTrue(m_region2.equals(m_region3));
        assertFalse(m_region2.equals(m_region4));
        assertFalse(m_region2.equals(m_region5));
        assertFalse(m_region2.equals(m_region6));
        assertFalse(m_region2.equals(m_region7));
        assertTrue(m_region2.equals(m_region8));
        assertFalse(m_region2.equals(m_region9));
        assertFalse(m_region2.equals(m_region10));
        assertFalse(m_region2.equals(m_region11));
        assertFalse(m_region2.equals(m_region12));
        
        assertFalse(m_region4.equals(m_region1)); // 2
        assertFalse(m_region4.equals(m_region5));
        assertFalse(m_region4.equals(m_region8));
        assertFalse(m_region4.equals(m_region9));
        assertFalse(m_region4.equals(m_region10));
        
        assertTrue(m_region5.equals(m_region6));
        assertTrue(m_region5.equals(m_region7));
        assertTrue(m_region5.equals(m_region11));
        assertTrue(m_region5.equals(m_region12));
        assertFalse(m_region5.equals(m_region4)); // 3
        assertFalse(m_region5.equals(m_region8));
        assertFalse(m_region5.equals(m_region9));
        assertFalse(m_region5.equals(m_region10));
        
        assertTrue(m_region6.equals(m_region5));
        assertTrue(m_region6.equals(m_region7));
        
        assertTrue(m_region7.equals(m_region11));
        assertTrue(m_region7.equals(m_region5));
        assertTrue(m_region7.equals(m_region6));
        
        assertFalse(m_region8.equals(m_region9));
        assertFalse(m_region8.equals(m_region10));
        
        assertFalse(m_region9.equals(m_region1));
        assertFalse(m_region9.equals(m_region4));
        assertFalse(m_region9.equals(m_region5));
        assertFalse(m_region9.equals(m_region8));
        assertFalse(m_region9.equals(m_region10));
        
        assertFalse(m_region10.equals(m_region1));
        assertFalse(m_region10.equals(m_region4));
        assertFalse(m_region10.equals(m_region5));
        assertFalse(m_region10.equals(m_region8));
        assertFalse(m_region10.equals(m_region9));
    }

    /**
     * Test of hashCode method, of class Region.
     */
    @Test
    public void testHashCode() {
        assertEquals(m_region1.hashCode(), m_region1.hashCode());
        assertEquals(m_region1.hashCode(), m_region2.hashCode());
        assertEquals(m_region1.hashCode(), m_region3.hashCode());
        assertEquals(m_region1.hashCode(), m_region8.hashCode());
        
        assertEquals(m_region2.hashCode(), m_region1.hashCode());
        assertEquals(m_region2.hashCode(), m_region2.hashCode());
        assertEquals(m_region2.hashCode(), m_region3.hashCode());
        assertEquals(m_region2.hashCode(), m_region8.hashCode());
        
        assertEquals(m_region5.hashCode(), m_region6.hashCode());
        assertEquals(m_region5.hashCode(), m_region7.hashCode());
        assertEquals(m_region5.hashCode(), m_region11.hashCode());
        assertEquals(m_region5.hashCode(), m_region12.hashCode());
        
        assertEquals(m_region6.hashCode(), m_region5.hashCode());
        assertEquals(m_region6.hashCode(), m_region7.hashCode());
        
        assertEquals(m_region7.hashCode(), m_region11.hashCode());
        assertEquals(m_region7.hashCode(), m_region5.hashCode());
        assertEquals(m_region7.hashCode(), m_region6.hashCode());
    }

    @Test
    public void testHashSet() {
        HashSet<Region> rgns = new HashSet<>();
        rgns.add(m_region1);
        rgns.add(m_region2);
        rgns.add(m_region3);
        rgns.add(m_region4);
        rgns.add(m_region5);
        rgns.add(m_region6);
        rgns.add(m_region7);
        rgns.add(m_region8);
        rgns.add(m_region9);
        rgns.add(m_region10);
        rgns.add(m_region11);
        rgns.add(m_region12);
        assertEquals(5, rgns.size());
        assertEquals(5, rgns.size());
        assertTrue(rgns.contains(m_region1));
        assertTrue(rgns.contains(m_region2));
        assertTrue(rgns.contains(m_region3));
        assertTrue(rgns.contains(m_region4));
        assertTrue(rgns.contains(m_region5));
        assertTrue(rgns.contains(m_region6));
        assertTrue(rgns.contains(m_region7));
        assertTrue(rgns.contains(m_region8));
        assertTrue(rgns.contains(m_region9));
        assertTrue(rgns.contains(m_region10));
        assertFalse(rgns.contains(null));
        assertFalse(rgns.contains(new Region(Arrays.asList(new Zone[]{ ZoneTest.m_zone8 }))));
        assertFalse(rgns.contains(new Region(Arrays.asList(new Zone[]{ ZoneTest.m_zone8, ZoneTest.m_zone5 }))));
        assertFalse(rgns.contains(new Region(Arrays.asList(new Zone[]{ ZoneTest.m_zone8, ZoneTest.m_zone5, ZoneTest.m_zone1 }))));
        assertTrue(rgns.contains(new Region(Arrays.asList(new Zone[]{ ZoneTest.m_zone8, ZoneTest.m_zone5, ZoneTest.m_zone1, ZoneTest.m_zone6 }))));
        assertFalse(rgns.contains(new Region(Arrays.asList(new Zone[]{ ZoneTest.m_zone8, ZoneTest.m_zone5, ZoneTest.m_zone1, ZoneTest.m_zone6, ZoneTest.m_zone3 }))));
        assertTrue(rgns.contains(new Region(Arrays.asList(new Zone[]{ ZoneTest.m_zone8, ZoneTest.m_zone5, ZoneTest.m_zone1, ZoneTest.m_zone6, ZoneTest.m_zone3, ZoneTest.m_zone7 }))));
        assertTrue(rgns.contains(new Region(Arrays.asList(new Zone[]{ }))));
    }

    /**
     * Test of isSubregionOf method, of class Region.
     */
    @Test
    public void testIsSubregionOf() {
        assertTrue(m_region1.isSubregionOf(m_region1));
        assertTrue(m_region2.isSubregionOf(m_region2));
        assertTrue(m_region3.isSubregionOf(m_region3));
        assertTrue(m_region4.isSubregionOf(m_region4));
        assertTrue(m_region5.isSubregionOf(m_region5));
        assertTrue(m_region6.isSubregionOf(m_region6));
        assertTrue(m_region7.isSubregionOf(m_region7));
        assertTrue(m_region8.isSubregionOf(m_region8));
        assertTrue(m_region9.isSubregionOf(m_region9));
        assertTrue(m_region10.isSubregionOf(m_region10));
        assertTrue(m_region11.isSubregionOf(m_region11));
        assertTrue(m_region12.isSubregionOf(m_region12));
        
        assertTrue(m_region2.isSubregionOf(m_region1));
        assertTrue(m_region3.isSubregionOf(m_region1));
        assertTrue(m_region4.isSubregionOf(m_region1));
        assertTrue(m_region5.isSubregionOf(m_region1));
        assertTrue(m_region6.isSubregionOf(m_region1));
        assertTrue(m_region7.isSubregionOf(m_region1));
        assertTrue(m_region8.isSubregionOf(m_region1));
        assertTrue(m_region9.isSubregionOf(m_region1));
        assertTrue(m_region10.isSubregionOf(m_region1));
        assertTrue(m_region11.isSubregionOf(m_region1));
        assertTrue(m_region12.isSubregionOf(m_region1));
        
        assertTrue(m_region2.isSubregionOf(m_region2));
        assertTrue(m_region3.isSubregionOf(m_region2));
        assertTrue(m_region4.isSubregionOf(m_region2));
        assertTrue(m_region5.isSubregionOf(m_region2));
        assertTrue(m_region6.isSubregionOf(m_region2));
        assertTrue(m_region7.isSubregionOf(m_region2));
        assertTrue(m_region8.isSubregionOf(m_region2));
        assertTrue(m_region9.isSubregionOf(m_region2));
        assertTrue(m_region10.isSubregionOf(m_region2));
        assertTrue(m_region11.isSubregionOf(m_region2));
        assertTrue(m_region12.isSubregionOf(m_region2));
        
        assertTrue(m_region5.isSubregionOf(m_region1));
        assertTrue(m_region5.isSubregionOf(m_region2));
        assertTrue(m_region5.isSubregionOf(m_region3));
        assertTrue(m_region5.isSubregionOf(m_region4));
        assertTrue(m_region6.isSubregionOf(m_region5));
        assertTrue(m_region5.isSubregionOf(m_region6));
        assertTrue(m_region5.isSubregionOf(m_region7));
        assertTrue(m_region5.isSubregionOf(m_region8));
        assertTrue(m_region5.isSubregionOf(m_region9));
        assertTrue(m_region5.isSubregionOf(m_region10));
        assertTrue(m_region5.isSubregionOf(m_region11));
        assertTrue(m_region5.isSubregionOf(m_region12));
        
        assertTrue(m_region10.isSubregionOf(m_region1));
        assertTrue(m_region10.isSubregionOf(m_region2));
        assertTrue(m_region10.isSubregionOf(m_region3));
        assertTrue(m_region10.isSubregionOf(m_region4));
        assertTrue(m_region10.isSubregionOf(m_region8));
        assertTrue(m_region10.isSubregionOf(m_region9));
        assertFalse(m_region10.isSubregionOf(m_region5));
        assertFalse(m_region10.isSubregionOf(m_region6));
        assertFalse(m_region10.isSubregionOf(m_region7));
        assertFalse(m_region10.isSubregionOf(m_region11));
        assertFalse(m_region10.isSubregionOf(m_region12));
        
        assertTrue(m_region4.isSubregionOf(m_region1));
        assertTrue(m_region4.isSubregionOf(m_region2));
        assertTrue(m_region4.isSubregionOf(m_region3));
        assertTrue(m_region4.isSubregionOf(m_region4));
        assertFalse(m_region4.isSubregionOf(m_region5));
        assertFalse(m_region4.isSubregionOf(m_region6));
        assertFalse(m_region4.isSubregionOf(m_region7));
        assertTrue(m_region4.isSubregionOf(m_region8));
        assertFalse(m_region4.isSubregionOf(m_region9));
        assertFalse(m_region4.isSubregionOf(m_region10));
        assertFalse(m_region4.isSubregionOf(m_region11));
        assertFalse(m_region4.isSubregionOf(m_region12));
    }
}
