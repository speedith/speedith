package spiderdrawer.shape;

import java.awt.Color;
import java.awt.Graphics2D;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

import spiderdrawer.exception.EmptyContainerException;
import spiderdrawer.shape.containers.MultiContainer;
import spiderdrawer.shape.containers.SingleContainer;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Movable;
import spiderdrawer.shape.interfaces.Shape;
import static spiderdrawer.Parameters.*;

public class Point implements Drawable, Movable, Deletable {

	int x;
	int y;
	long time;
	Line line1;
	boolean line1Start;
	Line line2;
	boolean line2Start;
	private ArrayList<Shape> shapeList;
	MultiContainer<Circle, Point> circles;
	MultiContainer<Box, Point> boxes;
	Label label;
	SingleContainer<Spider, Point> spider;
	
	public Point(int x, int y) {
		this.x = x;
		this.y = y;
		time = (new Date()).getTime();
	}
	
	private void createContainers() {
		circles = new MultiContainer<Circle, Point>(this);
		boxes = new MultiContainer<Box, Point>(this);
		spider = new SingleContainer<Spider, Point>(this);
	}
	
	public static Point create(int x, int y, ArrayList<Shape> shapeList) {
		Point point = new Point(x, y);
		point.createContainers();
		point.shapeList = shapeList;
		point.recompute(false);
		return point;
	}
	
	public static Point create(Freeform freeform, ArrayList<Shape> shapeList) {
		int x = (freeform.minX() + freeform.maxX())/2;
		int y = (freeform.minY() + freeform.maxY())/2;
		return create(x, y, shapeList);
	}
	
	public float getTime() {
		return time;
	}
	
	public int getX() {
		return x;
	}
	
	public int getY() {
		return y;
	}
	
	protected Line getLine1() {
		return line1;
	}
	
	protected Line getLine2() {
		return line2;
	}
	
	public String asString() throws EmptyContainerException { //TODO: Need to check circles and excluded circles have labels, and deal with error better. 
		String result = "([";
		for (int i = 0; i < circles.size(); i++) {
			result += "\"" + circles.get(i).label.getWExc("Label").getChar() + "\"";
			if (i != circles.size()-1)
				result += ", ";
		}
		result += "],[";
		if (boxes.size() == 1) {
			Box box = boxes.get(0);
			if (!box.circles.containsAll(circles))
				System.out.println("ERROR: box doesn't contain all the circles that point is within.");
			List<Circle> excluded = box.circles.intersection(circles);
			for (int i = 0; i < excluded.size(); i++) {
				result += "\"" + excluded.get(i).label.getWExc("Label").getChar() + "\"";
				if (i != excluded.size()-1)
					result += ", ";
			}
		} else {
			System.out.println("ERROR: point not in single box.");
		}
		return result + "])";
	}
	
	public boolean isFullyConnected() {
		return (line1 != null) && (line2 != null);
	}
	
	protected int whichLine(Line line) { //0 for no line, 1 for line1, 2 for line2, 3 for both lines.
		if (line.equals(line1)) {
			return 1;
		} else if (line.equals(line2)){
			return 2;
		}
		return 0;
	}
	
	protected Line otherLine(Line line) { //0 for no line, 1 for line1, 2 for line2, 3 for both lines.
		if (line.equals(line1)) {
			return line2;
		} else if (line.equals(line2)){
			return line1;
		}
		return null;
	}
	
	protected int whichLineNull() { //0 for no line, 1 for line1, 2 for line2
		if (line1 == null) {
			return 1;
		} else if (line2 == null) {
			return 2;
		}
		return 0;
	}
	
	protected void setLine1(Line l, boolean start) {
		Line oldLine = line1;
		boolean oldLineStart = line1Start;
		line1 = l;
		line1Start = start;
		if (oldLine != null) {
			oldLine.setPoint(null, oldLineStart);
		}
		if (line1 != null && !this.equals(line1.getPoint(start))) {
			line1.setPoint(this, start);
		}
	}
	
	protected void setLine2(Line l, boolean start) {
		Line oldLine = line2;
		boolean oldLineStart = line2Start;
		if (oldLine != null) {
			oldLine.setPoint(null, oldLineStart);
		}
		
		line2 = l;
		line2Start = start;
		if (line2 != null && !this.equals(line2.getPoint(start))) {
			line2.setPoint(this, start);
		}
	}
	
	@Override
	public boolean isValid() {
		return !isPointSameCircle();
	}
	
	@Override
	public void draw(Graphics2D g2) {
		if (!isValid())
			g2.setColor(Color.RED);
		g2.fillOval(x-2, y-2, 4, 4);
		g2.drawOval(x-2, y-2, 4, 4);
		g2.setColor(Color.BLACK);
		if (label != null) {
			label.draw(g2);
		}
	}
	
	@Override
	public void move(Point from, Point to) {
		x += to.getX() - from.getX();
		y += to.getY() - from.getY();
		if (label != null)
			label.move(from, to);
	}
	
	protected void moveTo(Point to) {
		move(new Point(x, y), to);
	}
	
	protected double distance(Point p) {
		return Math.sqrt((this.x - p.x)*(this.x - p.x) + (this.y - p.y)*(this.y - p.y));
	}
	
	public double boundaryDistance(Point p) {
		return distance(p);
	}
	
	private void computeLines(Line[] lines) {
		int line1Pos = -1;
		int line2Pos = -1;
		boolean line1Start = false;
		boolean line2Start = false;
		double lowestDist1 = Double.MAX_VALUE;
		double lowestDist2 = Double.MAX_VALUE;
		for (int i = 0; i < lines.length; i++) {
			double startDist = lines[i].start.distance(this);
			if (lines[i].startSet)
				startDist = Double.MAX_VALUE;
			double endDist = lines[i].end.distance(this);
			if (lines[i].endSet)
				endDist = Double.MAX_VALUE;
			double dist;
			boolean closerStart;
			if (startDist < endDist) {
				dist = startDist;
				closerStart = true;
			} else {
				dist = endDist;
				closerStart = false;
			}
			
			if (dist < lowestDist1) {
				lowestDist2 = lowestDist1;
				line2Start = line1Start;
				line2Pos = line1Pos;
				lowestDist1 = dist;
				line1Start = closerStart;
				line1Pos = i;
			} else if (dist < lowestDist2) {
				lowestDist2 = dist;
				line2Start = closerStart;
				line2Pos = i;
			}
		}
		
		//If line1 is already connected to the dot.
		if (line1Pos != -1 && ((lines[line1Pos]).start.equals(this) || (lines[line1Pos]).end.equals(this))) {
			line1Pos = line2Pos;
			line1Start = line2Start;
			lowestDist1 = lowestDist2;
			line2Pos = -1;
		}
		
		if (line1 == null) {
			if (lowestDist1 <= POINT_LINE_DIST && line1Pos != -1 && !lines[line1Pos].isConnected(this)) {
				System.out.println("close to line 1 at " + ((line1Start)? "start" : "end"));
				this.setLine1(lines[line1Pos], line1Start);
			}
			if (line2 == null && lowestDist2 <= POINT_LINE_DIST && line2Pos != -1 && !lines[line2Pos].isConnected(this)) {
				System.out.println("close to line 2 at " + ((line2Start)? "start" : "end"));
				this.setLine2(lines[line2Pos], line2Start);
			}
		} else if (line2 == null) {
			if (lowestDist1 <= POINT_LINE_DIST && line1Pos != -1 && !lines[line1Pos].isConnected(this)) {
				System.out.println("close to line 2 at " + ((line1Start)? "start" : "end"));
				this.setLine2(lines[line1Pos], line1Start);
			}
		}
	}
	
	private void computeCircles(Circle[] circles) {
		this.circles.removeAll();
		for (int i = 0; i < circles.length; i++) {
			if (circles[i].distance(this) == 0) {
				this.circles.add(circles[i], circles[i].points);
			}
		}
	}
	
	private void computeBoxes(Box[] boxes) {
		this.boxes.removeAll();
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].contains(this) && boxes[i].innerBoxes.isEmpty()) {
				this.boxes.add(boxes[i], boxes[i].points);
			}
		}
	}

	@Override
	public void recompute(boolean moving) {
		if (shapeList == null)
			return;
		computeLines(Arrays.lineArray(shapeList));
		computeCircles(Arrays.circleArray(shapeList));
		computeBoxes(Arrays.boxArray(shapeList));
		computeSpider();
	}
	
	private void computeSpider() {
		if (line1 == null && line2 == null && spider.get() == null) {
			Spider spider = new Spider();
			spider.add(this);
		} else {
			if ((line1 != null && line1.spider.get() != null) && (line2 != null && line2.spider.get() != null) && !line1.spider.get().equals(spider.get()) && !line2.spider.get().equals(spider.get())) {
				Spider spiderl1 = line1.spider.get();
				spiderl1.points.add(this, this.spider);
				Spider tempSpider = line2.spider.get();
				spiderl1.add(line2.spider.get());
				tempSpider.remove();
			} else if (line1 != null && line1.spider.get() != null && !line1.spider.get().equals(spider.get())) { //line2.spider == null
				Spider tempSpider = spider.get();
				if (spider.get() == null) {
					line1.spider.get().add(this);
				} else {
					line1.spider.get().add(spider.get());
				}
				if (tempSpider != null)
					tempSpider.remove();
			} else if (line2 != null && line2.spider.get() != null && !line2.spider.get().equals(spider.get())) { //line1.spider == null
				Spider tempSpider = spider.get();
				if (spider.get() == null) {
					line2.spider.get().add(this);
				} else {
					line2.spider.get().add(spider.get());
				}
				if (tempSpider != null)
					tempSpider.remove();
			}
		}
		spider.get().computeBox();
	}
	
	protected boolean isPointSameCircle() {
		Line iterLine = this.line1;
		Point iterPoint = this;
		while (iterLine != null && iterLine.hasBothEnds()) {
			iterPoint = iterLine.otherEnd(iterPoint);
			if (iterPoint.circles.size() == this.circles.size() && iterPoint.circles.containsAll(this.circles))
				return true;
			iterLine = iterPoint.otherLine(iterLine);	
		}
		iterLine = this.line2;
		iterPoint = this;
		while (iterLine != null && iterLine.hasBothEnds()) {
			iterPoint = iterLine.otherEnd(iterPoint);
			if (iterPoint.circles.size() == this.circles.size() && iterPoint.circles.containsAll(this.circles))
				return true;
			iterLine = iterPoint.otherLine(iterLine);	
		}
		return false;
	}
	
	protected double dot(Point p) {
		return this.x*p.x + this.y*p.y;
	}
	
	protected Point minus(Point p) {
		return new Point(this.x - p.x, this.y - p.y);
	}
	
	protected Point plus(Point p) {
		return new Point(this.x + p.x, this.y + p.y);
	}

	@Override
	public boolean isWithin(Point p) {
		return this.distance(p) < POINT_MIN_DIST;
	}

	@Override
	public boolean intersects(Line line) {
		Circle circle = new Circle(x, y , 4);
		return circle.intersects(line);
	}
	
	public Spider getSpider() {
		return spider.get();
	}

	@Override
	public void remove() {
		Spider tempSpider = spider.get();
		spider.get().remove(this);
		if (label != null)
			tempSpider.setLabel(label.letter, label.number);
		this.setLine1(null, line1Start);
		this.setLine2(null, line2Start);
		circles.removeAll();
		boxes.removeAll();
	}

}
