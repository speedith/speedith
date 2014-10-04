package spiderdrawer.recognizer;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;

import spiderdrawer.shape.Freeform;
import spiderdrawer.shape.Point;

import com.hp.hpl.inkml.Brush;
import com.hp.hpl.inkml.Ink;
import com.hp.hpl.inkml.InkElement;
import com.hp.hpl.inkml.Trace;
import com.uoa.cs.ink.Packet;
import com.uoa.cs.ink.PacketProperty;
import com.uoa.cs.ink.Stroke;
import com.uoa.cs.recognizer.DataStructures.MyLibrary;
import com.uoa.cs.recognizer.utilities.Converters;
import com.uoa.cs.recognizer.weka.WekaClassifier;

public class RataRecognizer {

    private WekaClassifier classifier = null;

    public RataRecognizer(String file) {
       InputStream stream = null;
        try {
        	stream = getClass().getResourceAsStream(file);
			classifier = new WekaClassifier(stream);
		} catch (ClassNotFoundException | IOException e1) {
			e1.printStackTrace();
		}
    }
	
	public String classify(Freeform f) {
		Stroke stroke = traceToStroke(freeformToTrace(f));
    	return classifier.classifierClassify(stroke);
	}
	
	private int pixelsToHimetric(double input)
    {
        // convert the trace data to the device ("dev") unit which is -
        // HIMETRIC unit for TabletPC SDK and hence for the ISF format.
        // 1 HIMETRIC = 0.01 mm = 25.4/0.01 inches.
        // Finaly the data is divided by 96 PPI which is the typical screen resolution

        return (int) (input * (25.4 / 0.01 / ((float)127f)));
    }

    
	private int millisecondsToPacketTime(double input)
	{
		return (int) Converters.millisToWinTime(input);
	}
    
	private Trace freeformToTrace(final Freeform f) {
		Trace trace = new Trace();
    	Ink ink = new Ink();
    	ArrayList<Point> points = f.getPoints();
    	trace.setAssociatedContext(ink.getCurrentContext());
		
		Collection<InkElement> definitions = ink.getDefinitions().getChildrenList();
		for(InkElement elem : definitions)
		{
			if(elem instanceof com.hp.hpl.inkml.Brush && trace.getBrushRef().isEmpty())
				trace.setAttribute("brushRef", "#"+ ((Brush)elem).getId());
			
			if(elem instanceof com.hp.hpl.inkml.Context && trace.getContextRef().isEmpty())
				trace.setAttribute("contextRef", "#"+ ((com.hp.hpl.inkml.Context)elem).getId());
		} 
		trace.setTraceData("X", new float[] { points.get(0).getX() });
    	trace.setTraceData("Y", new float[] { points.get(0).getY() });
    	trace.setTraceData("T", new float[] { points.get(0).getTime() - points.get(0).getTime() });
    	for (int i = 1; i < points.size(); i++) {
    		
    		trace.addToTraceData("X", new float[] { points.get(i).getX() });
    		trace.addToTraceData("Y", new float[] { points.get(i).getY() });
    		trace.addToTraceData("T", new float[] { points.get(i).getTime() - points.get(0).getTime() });
    	}
    	return trace;
	}
	
    @SuppressWarnings({ "rawtypes", "unchecked" })
	private Stroke traceToStroke(final Trace t)
	{
		LinkedHashMap<String, ArrayList> traceData = t.getTraceData();
		if(traceData!=null)
		{
			ArrayList<Float> xs = traceData.get("X");
			ArrayList<Float> ys = traceData.get("Y");
			ArrayList<Float> ts = traceData.get("T");
	
			Stroke stroke = new Stroke(new com.uoa.cs.ink.Ink());
			int numPoints = xs.size();
			
			int initTime = -1;
			int lastTime = -1;
			for (int i = 0; i < numPoints; i++)
			{
				if(i==0)
					initTime = millisecondsToPacketTime(ts.get(i)); 
				
				int currentT = i==0 ? 0 : millisecondsToPacketTime(ts.get(i)) - initTime;
				
				if(i==numPoints-1)
					lastTime = currentT;
				
				int currentX = pixelsToHimetric(xs.get(i));
				int currentY = pixelsToHimetric(ys.get(i));
				
				
				Packet p = new Packet();
				p.set(PacketProperty.X, currentX);
				p.set(PacketProperty.Y, currentY);
				p.set(PacketProperty.TimerTick, currentT);
				stroke.addPacket(p);	
			}
			
			stroke.setExtendedProperty(MyLibrary.TIMEGUID, lastTime);
			return stroke;
		}
		else
		{
			return null;
		}
	}
}
