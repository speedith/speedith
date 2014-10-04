package spiderdrawer.ui;

import java.awt.AlphaComposite;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JPanel;
import javax.swing.Timer;


public class MessageBox extends JPanel implements ActionListener {

    private String message = null;
    private static final Timer timer = new Timer(100, null);
    private int mode = 1;
    private float DELTA = 0.1f;
    private float alpha = 0f;
    private int wait = 1500; //in ms

    public MessageBox(String message) {
    	this.message = message;
        this.setPreferredSize(new Dimension(256, 30));
        this.setBackground(Color.white);
        timer.setInitialDelay(1000);
        timer.addActionListener(this);
        timer.start();
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        if (timer.isRunning()) {
		    Graphics2D g2d = (Graphics2D) g;
		    g2d.setFont(new Font(g2d.getFont().getFontName(), Font.PLAIN, 14));	
		    int w2 = g.getFontMetrics().stringWidth(message) / 2;
		    setSize(new Dimension(30+w2*2, 30));
		    int xx = this.getWidth();
		    int yy = this.getHeight();
		    int h2 = g.getFontMetrics().getDescent();
		    g2d.setComposite(AlphaComposite.getInstance(AlphaComposite.SRC_OVER, alpha));
		    g2d.setPaint(Color.gray);
		    g2d.fillRoundRect(0, 0, xx, yy, 15, 15);
		    g2d.setPaint(Color.white);
		    g2d.drawString(message, xx / 2 - w2, yy / 2 + h2);
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {    	
    	if (mode == 1) {
    		alpha += DELTA;
    	} else if (mode == 0) {
    		wait -= 100;
    		if (wait <= 0) {
    			mode = -1;
    		}
    	} else {
    		alpha -= DELTA;
    	}
    	
    	if (alpha >= 1 && mode != -1) {
    		mode = 0;
    		alpha = 1f;
    	} else if (alpha <= 1e-6 && mode == -1) {
    		alpha = 0;
    		timer.stop();
    	}
    	
        repaint();
    }
}