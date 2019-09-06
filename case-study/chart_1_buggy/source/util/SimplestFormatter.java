package util;

import java.util.logging.Formatter;
import java.util.logging.LogRecord;

public class SimplestFormatter extends Formatter {

	public String format(LogRecord log) {
		return log.getMessage()+"\n";
	}

}
