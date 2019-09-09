package util;

import java.util.logging.*;
import java.lang.reflect.Field;
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Modifier;


import org.aspectj.lang.Signature;
import org.aspectj.lang.reflect.*;

aspect Trace{

	private Logger logger;
	private Handler h;

	public void setupLogger() {
		if(logger == null){
			logger = Logger.getLogger("Tracer");
			logger.setLevel(Level.ALL);
		}
		try{
			if(h == null){
				h = new FileHandler(logger.getName()+".log",true);
				h.setLevel(Level.ALL);
				h.setFormatter(new SimplestFormatter());
				logger.addHandler(h);
			}
		}
		catch(Exception e){
			System.err.println(e.getStackTrace());
		}
	}

	after() returning(Object r) : execution(void org.jfree.chart.renderer.category.AbstractCategoryItemRenderer.*(..)) && !cflow(within(Trace)) {
		setupLogger();
		Event event = new Event(thisJoinPoint.getStaticPart().getSignature().getName(), thisJoinPoint.getArgs());
		event.setThis(thisJoinPoint.getThis());
		logger.log(Level.FINE, event.toString());
	}

	after() returning(Object r) : execution(!void org.jfree.chart.renderer.category.AbstractCategoryItemRenderer.*(..)) && !cflow(within(Trace)) {
		setupLogger();
		Event event = new Event(thisJoinPoint.getStaticPart().getSignature().getName(), thisJoinPoint.getArgs());
		event.setThis(thisJoinPoint.getThis());

		try {
			event.setOutputs(r);
		}
		catch(NullPointerException e) {
		}
		logger.log(Level.FINE, event.toString());
	}

	before() : execution(org.jfree.chart.renderer.category.AbstractCategoryItemRenderer.new(..)) && !within(Trace) {
		setupLogger();
		Object[] inputs = {thisJoinPoint.getThis()};
		Event event = new Event("new", inputs, inputs);
		logger.log(Level.FINE, event.toString());
	}

	before() : execution(* org.jfree.chart.renderer.category.junit.AbstractCategoryItemRendererTests.*(..)) && !cflow(within(Trace)) {
		setupLogger();
		logger.log(Level.FINE, "[TRACE]");
	}
}
