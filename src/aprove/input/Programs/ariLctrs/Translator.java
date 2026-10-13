package aprove.input.Programs.ariLctrs;

import java.io.*;

import org.antlr.runtime.*;

import aprove.input.Generated.ariLctrs.*;
import aprove.input.Utility.*;
import aprove.verification.dpframework.LCTRSProblem.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Translator.*;

/**
 * Translator for logically constrained TRSs in the ARI format. The result is an {@link LCTRSProblem}.
 * Files with the extension <code>ari</code> are passed on to this translator by
 * {@link aprove.input.Programs.ariTrs.Translator} if they declare the format LCTRS.
 */
public class Translator extends TranslatorSkeleton {

    @Override
    public Language getLanguage() {
        return Language.LCTRS;
    }

    @Override
    public void translate(final Reader reader) {
        try {
            final ariLctrsLexer lexer = new ariLctrsLexer(new ANTLRReaderStream(reader));
            final ariLctrsParser parser = new ariLctrsParser(new CommonTokenStream(lexer));
            final LctrsBuilder builder = new LctrsBuilder();
            parser.lctrs(builder);
            for (final RecognitionException re : lexer.getLexerErrors()) {
                this.addError(re, "Unexpected character");
            }
            final LCTRSProblem problem = builder.build();
            this.getErrors().addAll(builder.getErrors());
            if (!this.hasErrors()) {
                this.setState(problem);
            }
        } catch (final RecognitionException re) {
            this.addError(re, "Syntax error at " + (re.token == null ? "this position" : re.token.getText()));
        } catch (final IOException e) {
            final ParseError pe = new ParseError();
            pe.setMessage(e.getMessage());
            this.getErrors().add(pe);
        }
    }

    private void addError(final RecognitionException re, final String message) {
        final ParseError pe = new ParseError();
        pe.setLine(re.line);
        pe.setColumn(re.charPositionInLine);
        pe.setMessage(message);
        this.getErrors().add(pe);
    }

}
