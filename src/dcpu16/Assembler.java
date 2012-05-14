package dcpu16;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import util.Pair;


/**
 * Assembles a stream of DCPU-16 code. See {@linkplain http://0x10c.com/doc/dcpu-16.txt}.
 * 
 * <p>This class is not threadsafe.
 *
 * @author guitardave@gmail.com (David Byttow)
 */
public class Assembler {
  
  private static final String[] REGISTERS = { "A", "B", "C", "X", "Y", "Z", "I", "J" };
  private static final String[] SPECIAL_REGISTERS = { "SP", "PC", "O" };
  private static final String[] PROGRAM_OPS = { "POP", "PEEK", "PUSH", "SP", "PC", "O" };

  private static final String[] BASIC_OP_CODES = {
    "SET", "ADD", "SUB", "MUL", "DIV", "MOD", "SHL", "SHR", "AND",
    "BOR", "XOR", "IFE", "IFN", "IFG", "IFB"
  };

  private static final String[] NON_BASIC_OP_CODES = { "JSR" };

  private static final String LITERAL_REGEX_GROUP = "(?:0?x([a-fA-F0-9]+))|([0-9]+)";  
  private static final String REGISTER_REGEX_GROUP = "([a-cA-C]|[x-z|X-Z]|[i-jI-J])";
  private static final String IDENT_REGEX_GROUP = "([a-zA-Z]\\w+)";
  private static final String LABEL_DEF_REGEX_GROUP = "\\:" + IDENT_REGEX_GROUP;
  
  private static final Pattern ADDRESS_PATTERN = Pattern.compile("^\\[([\\w\\+]+)\\]$");
  private static final Pattern LITERAL_PATTERN = Pattern.compile("^" + LITERAL_REGEX_GROUP + "$");
  private static final Pattern IDENT_PATTERN = Pattern.compile("^" + IDENT_REGEX_GROUP + "$");
  private static final Pattern PLUS_REGISTER_PATTERN
      = Pattern.compile("^(" + LITERAL_REGEX_GROUP + ")\\s*\\+\\s*" + REGISTER_REGEX_GROUP + "$");

  private static final Pattern INSTRUCTION_PATTERN = Pattern.compile(
      "^(?:" + LABEL_DEF_REGEX_GROUP
      + "?\\s+)?([a-zA-Z]+)\\s+(\\[?[\\w\\+]+\\]?)[\\s*]?(?:,?[\\s*]?(\\[?.+\\]?))?$");    

  private static final short BACKFILL_MARKER = -1;
  
  private ArrayList<Short> byteCode;
  private Map<String, Short> labelMap;
  private ArrayList<Pair<Short, String>> backfills;

  /**
   * Assembles a stream of DCPU-16 assembly into a DCPU-16 byte code.
   * Adds padding to be row-length 8 aligned.
   *
   * @param stream the stream of text
   * @return array of raw byte code
   * @throws IOException if there was an IO error
   * @throws IllegalArgumentException if there was a program error
   */
  public short[] assemble(InputStream stream) throws IOException {
    BufferedReader reader = new BufferedReader(new InputStreamReader(stream));
    byteCode = new ArrayList<Short>();
    labelMap = new HashMap<String, Short>();
    backfills = new ArrayList<Pair<Short, String>>();

    // Iterate through the stream, line-by-line.
    for (String line = reader.readLine(); line != null; line = reader.readLine()) {
      String[] tokens = getTokens(line);
      if (tokens == null) {
        continue;
      }

      String label = tokens[0];
      if (label != null) {
        labelMap.put(label, (short) byteCode.size());
      }

      String opString = tokens[1];
      short op = getOpCode(opString);
      boolean basic = true;
      if (op == 0) {
        op = getNonBasicOpCode(opString);
        basic = false;
      }

      Pair<Short, Short> firstPart = basic
          ? getBasicOpValue(tokens[2]) : getNonBasicOpValue(tokens[2]);
      short a = firstPart.first();
      short b = 0;

      Pair<Short, Short> secondPart = null;
      if (!basic && tokens[3] != null && !tokens[3].isEmpty()) {
        secondPart = getBasicOpValue(tokens[3]);
        b = secondPart.first();
      }

      // Basic and non-basic op codes have distinct word formats.
      if (basic) {
        byteCode.add((short) ((b << 10) | (a << 4) | (op & 0xffff)));
      } else {
        byteCode.add((short) ((a << 10) | (op << 4)));
      }

      if (firstPart.second() != null) {
        byteCode.add(firstPart.second());
      }

      if (secondPart != null && secondPart.second() != null) {
        byteCode.add(secondPart.second());
      }      
    }
    
    // Now backfill.
    for (Pair<Short, String> pair : backfills) {
      String label = pair.second();
      Short pos = labelMap.get(label);
      if (pos == null) {
        throw new IllegalArgumentException("Unknown label: " + label);
      }
      for (int i = 0; i < 2; ++i) {
        int index = pair.first() + i + 1;
        if (index >= byteCode.size()) {
          continue;
        }
        if (byteCode.get(index) == BACKFILL_MARKER) {
          byteCode.set(index, pos);
        }
      }
    }

    // Emit the bytecode and add padding if necessary.
    int padding = byteCode.size() % 8;
    short[] program = new short[byteCode.size() + padding];
    int i = 0;
    for (short s : byteCode) {
      program[i++] = s;
    }
    
    while (padding-- > 0) {
      program[i++] = 0;
    }    
    return program;
  }
  
  private Pair<Short, Short> getBasicOpValue(String token) {
    int programIndex = findInArray(BASIC_OP_CODES, token);
    if (programIndex != -1) {
      return Pair.first((short) (0x18 + programIndex));
    }

    String addressToken = getAddressToken(token);
    boolean isAddress = (addressToken != null);
    if (isAddress) {
      token = addressToken;
    }

    int registerIndex = findInArray(REGISTERS, token);
    if (registerIndex != -1) {
      return Pair.first((short) (isAddress ? 0x08 + registerIndex : registerIndex));
    }
    
    int specialRegisterIndex = findInArray(SPECIAL_REGISTERS, token);
    if (specialRegisterIndex != -1) {
      if (isAddress) {
        throw new IllegalArgumentException("Address value of " + token + " is illegal");
      }
      return Pair.first((short) (0x1b + specialRegisterIndex));
    }
    
    int programOpsIndex = findInArray(PROGRAM_OPS, token);
    if (programOpsIndex != -1) {
      return Pair.first((short) (0x18 + programOpsIndex));
    }
    
    Short literalShort = getLiteralValue(token);
    if (literalShort != null) {
      short v = literalShort;
      if (v >= 0 && v <= 0x1f) {
        return Pair.first((short) (0x20 + v));
      }
      return Pair.of((short) (isAddress ? 0x1e : 0x1f), v);
    }

    Matcher plusRegisterMatcher = PLUS_REGISTER_PATTERN.matcher(token);
    if (plusRegisterMatcher.matches()) {
      short v = getLiteralValue(plusRegisterMatcher.group(1));
      registerIndex = findInArray(REGISTERS, plusRegisterMatcher.group(4));
      if (registerIndex == -1) {
        throw new IllegalArgumentException("Expected valid register: " + token);
      }
      return Pair.of((short) (0x10 + registerIndex), v);
    }

    Pair<Short, Short> backfilled = getBackfilledLabel(token);
    if (backfilled != null) {
      return backfilled;
    }
    
    throw new IllegalArgumentException("Unhandled line: " + token);
  }

  private Pair<Short, Short> getNonBasicOpValue(String token) {
    return getBackfilledLabel(token);
  }
  
  private Pair<Short, Short> getBackfilledLabel(String token) {
    Matcher m = IDENT_PATTERN.matcher(token);
    if (m.matches()) {
      backfills.add(Pair.of((short) byteCode.size(), m.group(1)));
      return Pair.of((short) 0x1f, BACKFILL_MARKER);
    }
    return null;
  }

  private Short getLiteralValue(String token) {
    Matcher m = LITERAL_PATTERN.matcher(token);
    if (!m.matches()) {
      return null;
    }

    int base = 10;
    if (m.group(1) != null) {
      base = 16;
      token = m.group(1);
    } else {
      token = m.group(2);
    }
    try {
      return Short.parseShort(token, base);
    } catch (IllegalArgumentException e) {
      throw new IllegalArgumentException("Invalid number: " + token, e);
    }
  }
  
  private static String getAddressToken(String token) {
    Matcher matcher = ADDRESS_PATTERN.matcher(token);
    if (matcher.matches()) {
      return matcher.group(1);
    }
    return null;
  }

  private static short getOpCode(String token) {
    return (short) (findInArray(BASIC_OP_CODES, token) + 1);
  }
  
  private static short getNonBasicOpCode(String token) {
    int index = findInArray(NON_BASIC_OP_CODES, token);
    if (index == -1) {
      throw new IllegalArgumentException("Unknown operation: " + token);
    }
    return (short) (index + 1);
  }
  
  private static int findInArray(String[] values, String value) {
    for (int i = 0; i < values.length; ++i) {
      if (values[i].equals(value)) {
        return i;
      }
    }
    return -1;
  }

  private static String[] getTokens(String line) {
    int index = line.indexOf(';');
    if (index >= 0) {
      line = line.substring(0, index);
    }
    
    if (line.isEmpty()) {
      return null;
    }

    Matcher m = INSTRUCTION_PATTERN.matcher(line);
    ArrayList<String> tokens = new ArrayList<String>();
    if (!m.matches()) {
      throw new IllegalArgumentException("Invalid line: " + line);
    }
    
    for (int i = 0; i < m.groupCount(); ++i) {
      String match = m.group(i + 1);
      if (match != null) {
        match = match.trim();
      }
      tokens.add(match);
    }

    if (tokens.get(1) == null || tokens.get(2) == null) {
      throw new IllegalArgumentException("Invalid line: " + line);
    }
    return tokens.toArray(new String[tokens.size()]);
  }
}
