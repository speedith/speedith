package spiderdrawer;

import static org.junit.Assert.*;

import org.junit.Test;

import spiderdrawer.shape.Freeform;

public class OverlapsTest {

	
	
	@Test
	public void doOverlap() {	
		Freeform freeform1 = new Freeform(4,5);
		freeform1.addPoint(15,12);
		Freeform freeform2 = new Freeform(12,4);
		freeform2.addPoint(9,15);
		assertTrue(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void dontOverlap() {
		Freeform freeform1 = new Freeform(4,5);
		freeform1.addPoint(15,12);
		Freeform freeform2 = new Freeform(12,4);
		freeform2.addPoint(15,9);
		assertFalse(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void secondOverlap() {
		Freeform freeform1 = new Freeform(4,5);
		freeform1.addPoint(26,19);
		Freeform freeform2 = new Freeform(12,4);
		freeform2.addPoint(15,9);
		assertFalse(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void twoPointsOverlap() {
		Freeform freeform1 = new Freeform(4,5);
		freeform1.addPoint(4,5);
		Freeform freeform2 = new Freeform(4,5);
		freeform2.addPoint(4,5);
		assertTrue(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void firstVerticalDoOverlap() {
		Freeform freeform1 = new Freeform(4,5);
		freeform1.addPoint(4,15);
		Freeform freeform2 = new Freeform(0,5);
		freeform2.addPoint(10,10);
		assertTrue(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void firstVerticalDontOverlap() {
		Freeform freeform1 = new Freeform(4,8);
		freeform1.addPoint(4,15);
		Freeform freeform2 = new Freeform(0,5);
		freeform2.addPoint(10,10);
		assertFalse(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void secondVerticalDoOverlap() {
		Freeform freeform1 = new Freeform(0,5);
		freeform1.addPoint(10,10);
		Freeform freeform2 = new Freeform(4,5);
		freeform2.addPoint(4,15);
		assertTrue(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void secondVerticalDontOverlap() {
		Freeform freeform1 = new Freeform(0,5);
		freeform1.addPoint(10,10);		
		Freeform freeform2 = new Freeform(4,8);
		freeform2.addPoint(4,15);
		assertFalse(freeform1.overlaps(freeform2, 0));
	}

	@Test
	public void bothVerticalDoOverlap() {
		Freeform freeform1 = new Freeform(4,1);
		freeform1.addPoint(4,5);
		Freeform freeform2 = new Freeform(4,5);
		freeform2.addPoint(4,15);
		assertTrue(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void bothVerticalSeperateDontOverlap() {
		Freeform freeform1 = new Freeform(5,1);
		freeform1.addPoint(5,5);
		Freeform freeform2 = new Freeform(5,5);
		freeform2.addPoint(5,15);
		assertTrue(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void bothVerticalDontOverlap() {
		Freeform freeform1 = new Freeform(4,1);
		freeform1.addPoint(4,4);		
		Freeform freeform2 = new Freeform(4,5);
		freeform2.addPoint(4,15);
		assertFalse(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void parallelDoOverlap() {
		Freeform freeform1 = new Freeform(4,1);
		freeform1.addPoint(12,9);
		Freeform freeform2 = new Freeform(0,-3);
		freeform2.addPoint(4,1);
		assertTrue(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void parallelDontOverlap() {
		Freeform freeform1 = new Freeform(4,1);
		freeform1.addPoint(12,9);
		Freeform freeform2 = new Freeform(13,10);
		freeform2.addPoint(20,17);
		assertFalse(freeform1.overlaps(freeform2, 0));
	}
	
	@Test
	public void distanceDoOverlap() {
		Freeform freeform1 = new Freeform(0,0);
		freeform1.addPoint(5,5);
		Freeform freeform2 = new Freeform(3,2);
		freeform2.addPoint(6, 5);
		assertTrue(freeform1.overlaps(freeform2, 1));
	}
	
	@Test
	public void distanceOverlapTest() {
		Freeform freeform1 = new Freeform(325, 75);
		freeform1.addPoint(325, 75);
		Freeform freeform2 = new Freeform(179,70);
		freeform2.addPoint(180, 70);
		assertFalse(freeform1.overlaps(freeform2, 5));
	}
	
}
