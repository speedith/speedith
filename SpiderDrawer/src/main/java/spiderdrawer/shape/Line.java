package spiderdrawer.shape;

import java.awt.Color;
import java.awt.Graphics2D;
import java.util.ArrayList;

import spiderdrawer.exception.EmptyContainerException;
import spiderdrawer.shape.containers.MultiContainer;
import spiderdrawer.shape.containers.SingleContainer;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Movable;
import spiderdrawer.shape.interfaces.Shape;
import static spiderdrawer.Parameters.POINT_LINE_DIST;
import static spiderdrawer.Parameters.DIST_LINE_MOVE_END;

public class Line implements Drawable, Movable, Deletable {

	Point start;
	Point end;
	boolean startSet;
	boolean endSet;
	private ArrayList<Shape> shapeList;
	Point lastMovedTo;
	double lastDistAlong;
	MultiContainer<Box, Line> boxes;
	MultiContainer<Box, Line> overlapBoxes;
	SingleContainer<Spider, Line> spider;
	
	public Line (Point start, Point end) {
		this.start = start;
		this.end = end;
	}
	
	public Line(int startX, int startY, int endX, int endY) {
		this(new Point(startX, startY), new Point(endX, endY));
	}
	
	private void createContainers() {
		boxes = new MultiContainer<Box, Line>(this);
		overlapBoxes = new MultiContainer<Box, Line>(this);
		spider = new SingleContainer<Spider, Line>(this);
	}
	
	public static Line create(int startX, int startY, int endX, int endY, ArrayList<Shape> shapeList) {
		Line line = new Line(startX, startY, endX, endY);
		line.createContainers();
		line.shapeList = shapeList;
		line.recompute(false);
		return line;
	}
	
	public static Line create(Point start, Point end, ArrayList<Shape> shapeList) {
		return create(start.x, start.y, end.x, end.y, shapeList);
	}
	
	
	public static Line create(Freeform freeform, ArrayList<Shape> shapeList) {
		return create(freeform.points.get(0), freeform.points.get(freeform.points.size() - 1), shapeList);
	}
	
	protected boolean hasBothEnds() {
		return startSet && endSet;
	}
	
	protected Point otherEnd(Point point) {
		if (point == end) {
			return start;
		} else if (point == start) {
			return end;
		}
		return null;
	}
	
	protected boolean isSet(boolean start) {
		return (start)? this.startSet : this.endSet;
	}
	
	protected boolean atStart(Point point) {
		return (point.equals(start))? true : false;
	}
	
	public boolean isConnected(Point point) {
		return isConnected(point, this.startSet);
	}
	
	public boolean isConnected(Point point, boolean atStart) {
		Line line = this;
		while (line.isSet(atStart)) {
			Point otherPoint = line.getPoint(atStart);
			if (point.equals(otherPoint))
				return true;
			if (!otherPoint.isFullyConnected())
				return false;
			line = otherPoint.otherLine(line);
			atStart = !line.atStart(otherPoint);
		}
		return false;
	}
	
	private void computePoints(Point[] points) {
		int startPos = -1;
		int endPos = -1;
		double minStartDist = Double.MAX_VALUE;
		double minEndDist = Double.MAX_VALUE;
		for (int i = 0; i < points.length; i++) {
			if (points[i].isFullyConnected()) {
				continue;
			}
			double startDist = this.start.distance(points[i]);
			double endDist = this.end.distance(points[i]);
			if (startDist < endDist && startDist < minStartDist) {
				minStartDist = startDist;
				startPos = i;
			} else if (endDist < minEndDist ){
				minEndDist = endDist;
				endPos = i;
			}
		}
		
		if (!startSet && minStartDist <= POINT_LINE_DIST && startPos != -1) {
			this.setPoint(points[startPos], true);
		}
		
		if (!endSet && minEndDist <= POINT_LINE_DIST && endPos != -1 && !isConnected(points[endPos])) {
			this.setPoint(points[endPos], false);
		}
	}
	
	private void computeOverlapBoxes(Box[] boxes) {
		overlapBoxes.removeAll();
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].intersects(this)) {
				overlapBoxes.add(boxes[i], boxes[i].overlapLines);
			}
		}
	}
	
	private void computeBoxes(Box[] boxes) {
		this.boxes.removeAll();
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].contains(this) && boxes[i].innerBoxes.isEmpty()) {
				this.boxes.add(boxes[i], boxes[i].lines);
			}
		}
	}
	
	@Override
	public void recompute(boolean moving) {
		if (shapeList == null)
			return;		
		if (startSet) {
			start.recompute(moving);
		}
		
		if (endSet) {
			end.recompute(moving);
		}
		computePoints(Arrays.pointArray(shapeList));
		computeBoxes(Arrays.boxArray(shapeList));
		computeOverlapBoxes(Arrays.boxArray(shapeList));
		computeSpider();
	}
	
	private void computeSpider() {
		if (spider.get() == null && !startSet && !endSet) {
			Spider spider = new Spider();
			spider.add(this);
		} else {
			if ((startSet && start.spider.get() != null) && (endSet && end.spider.get() != null) && !start.spider.get().equals(spider.get()) && !end.spider.get().equals(spider.get())) {
				Point start, end;
				if ((this.start.spider.get().label == null || this.end.spider.get().label == null) || this.start.spider.get().label.number < this.end.spider.get().label.number) {
					start = this.start;
					end = this.end;
				} else {
					start = this.end;
					end = this.start;
				}
				Spider spiderS = start.spider.get();
				spiderS.lines.add(this, this.spider);
				Spider tempSpider = end.spider.get();
				spiderS.add(end.spider.get());
				tempSpider.remove();
			} else if (startSet && start.spider.get() != null && !start.spider.get().equals(spider.get())) { //line2.spider == null
				Spider tempSpider = spider.get();
				if (spider.get() == null) {
					start.spider.get().add(this);
				} else {
					start.spider.get().add(spider.get());
				}
				if (tempSpider != null)
					start.spider.get().add(tempSpider);
			} else if (endSet && end.spider.get() != null && !end.spider.get().equals(spider.get())) { //line2.spider == null
				Spider tempSpider = spider.get();
				if (spider.get() == null) {
					end.spider.get().add(this);
				} else {
					end.spider.get().add(spider.get());
				}
				if (tempSpider != null)
					end.spider.get().add(tempSpider);
			}
		}
		spider.get().computeBox();
	}
	
	protected void setPoint(Point point, boolean start) {
		if (start) {
			if (point != null) {
				Point oldStart = this.start;
				this.start = point;
				startSet = true;
				if (oldStart != null) {
					int lineNum = oldStart.whichLine(this);
					if (lineNum == 1) {
						oldStart.setLine1(null, start);
					} else if (lineNum == 2) {
						oldStart.setLine2(null, start);
					}
				}
				int lineNum = point.whichLine(this);
				if (lineNum == 0) {
					this.start.moveTo(oldStart);
					lineNum = point.whichLineNull();
				}
				
				if (lineNum == 1) {
					Line line = point.getLine1();
					if (!this.equals(line)) {
						point.setLine1(this, start);
					}
				}
				if (lineNum == 2) {
					Line line = point.getLine2();
					if (!this.equals(line)) {
						point.setLine2(this, start);
					}
				}
			} else {
				Point oldStart = this.start;
				this.start = new Point(this.start.getX(), this.start.getY());
				startSet = false;
				if (oldStart != null) {
					int lineNum = oldStart.whichLine(this);
					if (lineNum == 1) {
						oldStart.setLine1(null, start);
					} else if (lineNum == 2) {
						oldStart.setLine2(null, start);
					}
				}
			}
		} else {
			if (point != null) {
				Point oldEnd = this.end;
				this.end = point;
				endSet = true;
				if (oldEnd != null) {
					int lineNum = oldEnd.whichLine(this);
					if (lineNum == 1) {
						oldEnd.setLine1(null, start);
					} else if (lineNum == 2) {
						oldEnd.setLine2(null, start);
					}
				}
				int lineNum = point.whichLine(this);
				if (lineNum == 0) {
					this.end.moveTo(oldEnd);
					lineNum = point.whichLineNull();
				}
				
				if (lineNum == 1) {
					Line line = point.getLine1();
					if (!this.equals(line)) {
						point.setLine1(this, start);
					}
				}
				if (lineNum == 2) {
					Line line = point.getLine2();
					if (!this.equals(line)) {
						point.setLine2(this, start);
					}
				}
			} else {
				Point oldEnd = this.end;
				this.end = new Point(this.end.getX(), this.end.getY());
				endSet = false;
				if (oldEnd != null) {
					int lineNum = oldEnd.whichLine(this);
					if (lineNum == 1) {
						oldEnd.setLine1(null, start);
					} else if (lineNum == 2) {
						oldEnd.setLine2(null, start);
					}
				}
			}
		}
		
		
	}
	
	protected Point getPoint(boolean start) {
		if (start) {
			return this.start;
		} else {
			return this.end;
		}
	}
	
	protected boolean equalPointCircles() { //Assume both ends set.
		if (this.start.circles == null && this.end.circles == null) {
			return true;
		} else if ((this.start.circles != null && this.end.circles == null) || (this.start.circles == null && this.end.circles != null)) {
			return false;
		} else {
			if (this.start.circles.containsAll(this.end.circles) && this.end.circles.containsAll(this.start.circles)) {
				return true;
			} else if (this.start.circles.size() == 0 && this.end.circles.size() == 0){
				return true;
			}
			return false;
		}
	}
	
	@Override
	public boolean isValid() {
		return hasBothEnds() && !equalPointCircles() && overlapBoxes.isEmpty();
	}
	
	@Override
	public void draw(Graphics2D g2) {
		if (!isValid()) {
			g2.setColor(Color.RED);
		} else {
			g2.setColor(Color.BLACK);
		}
		g2.drawLine(start.getX(), start.getY(), end.getX(), end.getY());
		g2.setColor(Color.BLACK);
	}
	
	/* Algorithm:
	 *  P1 = this.start + t(this.end-this.start)
	 *  P2 = l.start + s(l.end - l.start)
	 *  P1 = P2
	 * 	Check if t and s in [0, 1]
	 */
	public boolean intersects(Line l) {
		int thisdx = this.end.x - this.start.x;
		int thisdy = this.end.y - this.start.y;
		int ldx = l.end.x - l.start.x;
		int ldy = l.end.y - l.start.y;
		
		if (thisdx == 0 && thisdy == 0 && ldx == 0 && ldy == 0) {			//Two Points
			if (this.start.x == l.start.x && this.start.y == l.start.y) { 	//Identical Points
				return true;
			} else {
				return false;
			}
		}
		
		int denom = ldx*thisdy - ldy*thisdx;
		if (denom == 0) {													//Parallel Lines	
			if (ldx != 0) {													//Not vertical lines
				double thisYintercept = this.start.y - (double)thisdy*this.start.x/thisdx;
				double lYintercept = l.start.y - (double)ldy*l.start.x/ldx;
				if (Math.abs(thisYintercept - lYintercept) <= 1e-6) {
					if (Math.min(this.start.x,this.end.x) >= Math.min(l.start.x, l.end.x) && Math.min(this.start.x,this.end.x) <= Math.max(l.start.x, l.end.x)
							 || Math.max(this.start.x,this.end.x) <= Math.max(l.start.x, l.end.x) && Math.max(this.start.x,this.end.x) >= Math.min(l.start.x, l.end.x)) {
								return true;
					}
				}
			}  else if (ldy != 0) {											//Not Horizontal Lines
				double thisXintercept = this.start.x - (double)thisdx*this.start.y/thisdy;
				double lXintercept = l.start.x - (double)ldx*l.start.y/ldy;
				if (Math.abs(thisXintercept - lXintercept) <= 1e-6) {
					if (Math.min(this.start.y,this.end.y) >= Math.min(l.start.y, l.end.y) && Math.min(this.start.y,this.end.y) <= Math.max(l.start.y, l.end.y)
							 || Math.max(this.start.y,this.end.y) <= Math.max(l.start.y, l.end.y) && Math.max(this.start.y,this.end.y) >= Math.min(l.start.y, l.end.y)) {
								return true;
					}
				}
			}
			return false;
		}
		
		int ltothis_start_dy = l.start.y - this.start.y;
		int ltothis_start_dx = l.start.x - this.start.x;
		double t = (double)(ltothis_start_dy*thisdx - ltothis_start_dx*thisdy)/denom;
		double s = (double)(ltothis_start_dy*ldx - ltothis_start_dx*ldy)/denom;
		
		if ((t >= 0 && t <= 1) && (s >= 0 && s <= 1)) {						//Intersect is in both segments
			return true;
		} else {
			return false;
		}
	}
	
	protected double distance(Circle c) {
		return Math.max(0,  this.distance(c.center) - c.getRadius());
	}
	
	public String asString() throws EmptyContainerException {
		return start.asString() + ", " + end.asString();
	}
	
	
	protected double distance(Line l) {
		if (intersects(l)) {
			return 0;
		}
		return Math.min(Math.min(this.start.distance(l.start), this.start.distance(l.end)), Math.min(this.end.distance(l.start), this.end.distance(l.end)));
	}
	
	protected double distance(Point p) {
		int thisdx = this.end.x - this.start.x;
		int thisdy = this.end.y - this.start.y;
		
		double t = distanceAlongLine(p);
		
		if (t <= 0) {										//Closer to start
			return this.start.distance(p);
		} else if (t >= 1) {								//Closer to end
			return this.end.distance(p);
		}
		Point intersect = new Point((int)Math.round(this.start.x + t*thisdx), (int)Math.round(this.start.y + t*thisdy));
		return intersect.distance(p);
	}
	
	public double boundaryDistance(Point p) {
		return distance(p);
	}
	
	public boolean isVertical() {
		return ((double)Math.abs(start.y - end.y)/(double)Math.abs(start.x - end.x) > 3);
	}
	
	protected double distanceAlongLine(Point p) {
		int thisdx = this.end.x - this.start.x;
		int thisdy = this.end.y - this.start.y;
		int ptothis_start_dx = p.x - this.start.x;
		int ptothis_start_dy = p.y - this.start.y;
		
		int denom = thisdx*thisdx + thisdy*thisdy;
		if (denom == 0) {									//Line is a single point
			return Math.sqrt(ptothis_start_dx*ptothis_start_dx + ptothis_start_dy*ptothis_start_dy);
		}
		
		return (double)(ptothis_start_dx*thisdx + ptothis_start_dy*thisdy)/denom;
	}


	public void move(Point from, Point to, boolean external) {
		if (external) {
			start.move(from, to);
			end.move(from, to);
		} else {
			move(from, to);
		}
	}
	
	public double length() {
		return Math.sqrt((start.x - end.x)*(start.x - end.x) + (start.y - end.y)*(start.y - end.y));
	}
	
	@Override
	public void move(Point from, Point to) {
		double distAlong;
		if (lastMovedTo == null || lastMovedTo.getX() != from.getX() || lastMovedTo.getX() != from.getX()) {
			distAlong = distanceAlongLine(from);
			lastDistAlong = distAlong;
		} else {
			distAlong = lastDistAlong;
		}
		lastMovedTo = to;
		if (distAlong < 1 - DIST_LINE_MOVE_END)
			start.move(from, to);
		if (distAlong > DIST_LINE_MOVE_END)
			end.move(from, to);
	}

	@Override
	public boolean isWithin(Point p) {
		return this.distance(p) < 4;
	}
	
	public Spider getSpider() {
		return spider.get();
	}

	@Override
	public void remove() {
		spider.get().remove(this);
		if (startSet) {
			this.setPoint(null, true);
		}
		if (endSet) {
			this.setPoint(null, false);
		}
		boxes.removeAll();
		overlapBoxes.removeAll();
	}
	
}
