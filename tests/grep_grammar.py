import string

from fuzzingbook.Grammars import Grammar, srange

GREP_GRAMMAR: Grammar = {
    "<start>":
        ["<printf>""<grep_env_var>""<program>""<command>"],

    "<printf>":
        ["printf ""<input_>"" | "],

    "<command>":
        ["<cmd_1><ws><patterns>"],

    "<cmd_1>":
        ["<general_options>"],

    "<program>":
        ["timeout 0.5s grep"],

    "<general_options>":
        ["<options>"],

    "<options>":
        ["<ws><matcher_selection><options>",
         "<ws><matching_control><options>",
         "<ws><output_control><options>",
         "<ws><output_line_prefix_control><options>",
         "<ws><context_line_control><options>",
         "<ws><file_and_dir_selection><options>",
         "<ws><other_options><options>",
         "<empty>"],

    "<patterns>":
        ["<pattern>", "-e <pattern>", "--regexp=<pattern>"],

    "<matcher_selection>":
        ["<extended_regex>", "<fixed_string>", "<regexp>"],

    "<matching_control>":
        ["<ignore_case>", "<invert_match>", "<word_match>", "<line_match>"],

    "<output_control>": ["<count>", "<color_opt_all>", "<files_matched>", "<files_not_matched>", "<max_count>",
                         "<only_match>", "<silent>", "<suppress_error_msg>"],

    "<output_line_prefix_control>": ["<byte_offset>", "<with_filename>", "<no_filename>", "<label>", "<line_no>",
                                     "<tab>", "<unix_byte_offset>", "<null>"],

    "<context_line_control>": ["<trail_context>", "<leading_context>", "<output_context>"],

    "<file_and_dir_selection>": ["<process_as_text>", "<binary_type>", "<devices>", "<directories>", "<exclude>",
                                 "<exclude_dir>", "<no_matching_data>", "<include>"],

    "<other_options>": ["<line_buf>", "<binary>", "<null_data>"],
    "<extended_regex>": ["-E", "--extended-regexp"],
    "<fixed_string>": ["-F", "--fixed-strings"],
    "<regexp>": ["-G", "--basic-regexp"],
    "<ignore_case>": ["-i", "--ignore-case", "-y"],
    "<invert_match>": ["-v", "--invert-match"],
    "<word_match>": ["-w", "--word-regexp"],
    "<line_match>": ["-x", "--line-regexp"],
    "<count>": ["-c", "--count"],
    "<color_opt_all>": ["<color_opt>", "<color_opt>""=""<color_when>"],
    "<color_opt>": ["--color", "--colour"],
    "<color_when>": ["always", "auto", "never"],
    "<files_matched>": ["-l", "--files-with-matches"],
    "<files_not_matched>": ["-L", "--files-without-match"],
    "<max_count>": ["-m ""<pos_number>", "--max-count=""<pos_number>"],
    "<only_match>": ["-o", "--only-matching"],
    "<silent>": ["-q", "--quiet", "--silent"],
    "<suppress_error_msg>": ["-s", "--no-messages"],
    "<byte_offset>": ["-b", "--byte-offset"],
    "<with_filename>": ["-H", "--with-filename"],
    "<no_filename>": ["-h", "--no-filename"],
    "<label>": ["'--label=""<label_str>""'"],
    "<line_no>": ["-n", "--line-number"],
    "<tab>": ["-T", "--initial-tab"],
    "<unix_byte_offset>": ["-u", "--unix-byte-offsets"],
    "<null>": ["-Z", "--null"],
    "<trail_context>": ["-A ""<pos_number>", "--after-context=""<pos_number>"],
    "<leading_context>": ["-B ""<pos_number>", "--before-context=""<pos_number>"],
    "<output_context>": ["-C ""<pos_number>", "-""<pos_number>", "--context=""<pos_number>"],
    "<process_as_text>": ["-a", "--text"],
    "<binary_type>": ["--binary-files=""<type>"],
    "<devices>": ["-D ""<action_devices>", "--devices=""<action_devices>"],
    "<directories>": ["-d ""<action_dir>", "--directories=""<action_dir>"],
    "<exclude>": ["'--exclude=""<glob>" "'"],
    "<exclude_dir>": ["'--exclude-dir=""<glob>""'"],
    "<no_matching_data>": ["-I"],
    "<include>": ["'--include=" "<glob>" "'"],
    "<line_buf>": ["--line-buffered"],
    "<binary>": ["-U", "--binary"],
    "<null_data>": ["-z", "--null-data"],
    "<empty>": [""],
    "<label_str>": ["<string>"],
    "<string>": ["<character>", "<character>""<string>"],
    "<type>": ["binary", "without-match", "text"],
    "<action_devices>": ["read", "skip"],
    "<action_dir>": ["read", "skip"],
    "<glob>": ["*""<glob>", "?""<glob>", "[""<glob>""],", "<string>", "\\""<glob>""\\", "<empty>"],

    "<ws>": [" "],

    #  TODO This deviates from the original grammar from Kampmann et al. as the fuzzer can not handle regex
    "<input_>": ["'" "<first_inputchar>" "<inputstring>" "'"],
    "<inputstring>": ["<inputchar>", "<inputchar><inputstring>", "<empty>"],
    "<first_inputchar>": ["<unicode_no_minus>"
        , "\\t", "\\n", "\\r", "\""
        , "\\x" "<hexdigit>" "<hexdigit>"
        , "\\" "<digit>" "<digit>" "<digit>"],
    "<inputchar>": ["-", "<first_inputchar>", "<unicode>"],

    "<unicode>": ["<uunicode>", "<unicode_chars>"],

    "<unicode_no_minus>": ["<unicode>"],

    "<unicode_chars>": srange(string.ascii_letters + string.digits),

    #  TODO can be improved?
    "<uunicode>": ["\\""u<bytes>"],
    "<bytes>": ["<byte>"],
    "<byte>": ["<zerof><zerof><zerof><zerof>"],
    "<zerof>": srange(string.digits + "ABCDEF"),

    "<hexdigit>": srange(string.digits + "ABCDEFabcdef"),

    "<grep_env_var>": ["<env_options>" "<ws>", "<empty>"],
    "<env_options>": ["<grep_color>", "<grep_colors>", "<locale_options>", "<posix_or_ignore_grep_operand>"],

    "<grep_color>": ["GREP_COLOR: ['" "<color>" "'"],
    "<color>": ["<sgr>"],
    "<sgr>": ["<digits>", "<digits>" "], " "<sgr>"],

    "<locale>": ["en_NZ", "nl_NL." "<utf8>", "pt_BR." "<utf8>", "fr_CH.ISO8859-15", "eu_ES.ISO8859-15",
                 "en_US.US-ASCII", "af_ZA", "bg_BG", "cs_CZ." "<utf8>", "fi_FI", "zh_CN." "<utf8>", "eu_ES",
                 "sk_SK.ISO8859-2", "nl_BE", "fr_BE", "sk_SK", "en_US." "<utf8>", "en_NZ.ISO8859-1", "de_CH",
                 "sk_SK." "<utf8>", "de_DE." "<utf8>", "am_ET." "<utf8>", "zh_HK", "be_BY." "<utf8>", "uk_UA",
                 "pt_PT.ISO8859-1", "en_AU.US-ASCII", "kk_KZ.PT154", "en_US", "nl_BE.ISO8859-15", "de_AT.ISO8859-1",
                 "hr_HR.ISO8859-2", "fr_FR.ISO8859-1", "af_ZA." "<utf8>", "am_ET", "fi_FI.ISO8859-1", "ro_RO." "<utf8>",
                 "af_ZA.ISO8859-15", "en_NZ." "<utf8>", "fi_FI." "<utf8>", "hr_HR." "<utf8>", "da_DK." "<utf8>",
                 "ca_ES.ISO8859-1", "en_AU.ISO8859-15", "ro_RO.ISO8859-2", "de_AT." "<utf8>", "pt_PT.ISO8859-15",
                 "sv_SE", "fr_CA.ISO8859-1", "fr_BE.ISO8859-1", "en_US.ISO8859-15", "it_CH.ISO8859-1",
                 "en_NZ.ISO8859-15", "en_AU." "<utf8>", "de_AT.ISO8859-15", "af_ZA.ISO8859-1", "hu_HU." "<utf8>",
                 "et_EE." "<utf8>", "he_IL." "<utf8>", "uk_UA.KOI8-U", "be_BY", "kk_KZ", "hu_HU.ISO8859-2", "it_CH",
                 "pt_BR", "ko_KR", "it_IT", "fr_BE." "<utf8>", "ru_RU.ISO8859-5", "zh_CN.GB2312", "no_NO.ISO8859-15",
                 "de_DE.ISO8859-15", "en_CA", "fr_CH." "<utf8>", "sl_SI." "<utf8>", "uk_UA.ISO8859-5", "pt_PT", "hr_HR",
                 "cs_CZ", "fr_CH", "he_IL", "zh_CN.GBK", "zh_CN.GB18030", "fr_CA", "pl_PL." "<utf8>", "ja_JP.SJIS",
                 "sr_YU.ISO8859-5", "be_BY.CP1251", "sr_YU.ISO8859-2", "sv_SE." "<utf8>", "sr_YU." "<utf8>",
                 "de_CH." "<utf8>", "sl_SI", "pt_PT." "<utf8>", "ro_RO", "en_NZ.US-ASCII", "ja_JP", "zh_CN",
                 "fr_CH.ISO8859-1", "ko_KR.eucKR", "be_BY.ISO8859-5", "nl_NL.ISO8859-15", "en_GB.ISO8859-1",
                 "en_CA.US-ASCII", "is_IS.ISO8859-1", "ru_RU.CP866", "nl_NL", "fr_CA.ISO8859-15", "sv_SE.ISO8859-15",
                 "hy_AM", "en_CA.ISO8859-15", "en_US.ISO8859-1", "ca_ES." "<utf8>", "ru_RU.CP1251", "en_GB." "<utf8>",
                 "en_GB.US-ASCII", "ru_RU." "<utf8>", "eu_ES." "<utf8>", "es_ES.ISO8859-1", "hu_HU", "el_GR.ISO8859-7",
                 "en_AU", "it_CH." "<utf8>", "en_GB", "sl_SI.ISO8859-2", "ru_RU.KOI8-R", "nl_BE." "<utf8>", "et_EE",
                 "fr_FR.ISO8859-15", "cs_CZ.ISO8859-2", "lt_LT." "<utf8>", "pl_PL.ISO8859-2", "fr_BE.ISO8859-15",
                 "is_IS." "<utf8>", "tr_TR.ISO8859-9", "da_DK.ISO8859-1", "lt_LT.ISO8859-4", "lt_LT.ISO8859-13",
                 "bg_BG.CP1251", "el_GR." "<utf8>", "be_BY.CP1131", "da_DK.ISO8859-15", "is_IS.ISO8859-15",
                 "no_NO.ISO8859-1", "nl_NL.ISO8859-1", "nl_BE.ISO8859-1", "sv_SE.ISO8859-1", "pt_BR.ISO8859-1",
                 "zh_CN.eucCN", "it_IT." "<utf8>", "en_CA." "<utf8>", "uk_UA." "<utf8>", "de_CH.ISO8859-15",
                 "de_DE.ISO8859-1", "ca_ES", "sr_YU", "hy_AM.ARMSCII-8", "ru_RU", "zh_HK." "<utf8>", "eu_ES.ISO8859-1",
                 "is_IS", "bg_BG." "<utf8>", "ja_JP." "<utf8>", "it_CH.ISO8859-15", "fr_FR." "<utf8>",
                 "ko_KR." "<utf8>", "et_EE.ISO8859-15", "kk_KZ." "<utf8>", "ca_ES.ISO8859-15", "en_IE." "<utf8>",
                 "es_ES", "de_CH.ISO8859-1", "en_CA.ISO8859-1", "es_ES.ISO8859-15", "en_AU.ISO8859-1", "el_GR", "da_DK",
                 "no_NO", "it_IT.ISO8859-1", "en_IE", "zh_HK.Big5HKSCS", "hi_IN.ISCII-DEV", "ja_JP.eucJP",
                 "it_IT.ISO8859-15", "pl_PL", "ko_KR.CP949", "fr_CA." "<utf8>", "fi_FI.ISO8859-15", "en_GB.ISO8859-15",
                 "fr_FR", "hy_AM." "<utf8>", "no_NO." "<utf8>", "es_ES." "<utf8>", "de_AT", "tr_TR." "<utf8>", "de_DE",
                 "lt_LT", "tr_TR", "C", "POSIX"],
    "<utf8>": ["utf8", "utf-8", "UTF-8"],

    "<locale_options>": ["<lc_all>" "<lc_options>" "<lang>"],
    "<lc_options>": ["<ws>" "<lc_collate>", "<ws>" "<lc_ctype>", "<ws>" "<lc_messages>", "<empty>"],
    "<lc_collate>": ["LC_COLLATE=" "<locale>"],
    "<lc_ctype>": ["LC_CTYPE=" "<locale>"],
    "<lc_messages>": ["LC_MESSAGES=" "<locale>"],
    "<lc_all>": ["LC_ALL=" "<locale>", "<empty>"],
    "<lang>": ["<ws>" "LANG=" "<locale>", "<empty>"],
    "<posix_or_ignore_grep_operand>": ["POSIXLY_CORRECT=1"],

    "<grep_colors>": ["GREP_COLORS='" "<grep_colors_value>" "'"],
    "<grep_colors_value>": ["<color_options>", "<color_options>" ":" "<grep_colors_value>", "<empty>"],
    "<color_options>": ["sl=" "<sgr>", "cx=" "<sgr>", "mt=01;31", "ms=01;31", "mc=01;31", "rv", "ne", "fn=35", "ln=32",
                        "bn=32", "se=36"],

    "<pos_number>": ["<nonzerodigit>" "<digits>", "<nonzerodigit>"],

    "<pattern>": ["'" "<regex_>" "'"],
    "<regex_>": ["<empty>", "<first_expression>" "<regex>"],
    "<regex>": ["<empty>", "<expression>" "<regex>"],

    "<first_expression>": ["<character_expr_no_minus>", "<bracket_expr>", "<special_expr>",
                           "<expression>" "<repetition>",
                           "<expression>" "|" "<expression>", "(" "<regex>" ")", "<back_reference>"],
    "<expression>": ["<character_expr>", "<bracket_expr>", "<special_expr>", "<expression>" "<repetition>",
                     "<expression>" "|" "<expression>", "(" "<regex>" ")", "<back_reference>"],
    "<character_expr>": srange(string.printable),

    "<character_expr_no_minus>": list(set(srange(string.printable)) - {"-"}),

    "<bracket_expr>": ["[" "<bracket_char_>" "]"
        , "[" "<bracket_char>" "-" "<bracket_char>" "]"
        , "[" "^" "<bracket_char_>" "]"
        , "[" "^" "<bracket_char>" "-" "<bracket_char>" "]"],
    "<special_expr>": ["\\<", "\\>", "\\b", "\\B", "\\w", "\\W"],
    "<repetition>": ["?", "*", "+", "{" "<int_>" "}", "{" "<int_>" ",}", "{," "<int_>" "}",
                     "{" "<int_>" "," "<int_>" "}"],
    "<back_reference>": ["\\" "<digit>"],
    "<bracket_char_>": ["<bracket_char>", "<bracket_char><bracket_char_>"],
    "<bracket_char>": ["<utf_characters>", "<alnum>", "<cntrl>", "<graph>", "<print>", "\"", "!", "#", "\\$",
                       "%", "&", "\\x27", "(", ")", "*", "+", ",", ".", "/", ":", ";", "<", "=", ">", "?", "@", "[",
                       "\\\\", "]", "^", "_", "`", "{", "|", "}", "~", "<space>"],
    "<digit>": ["<nonzerodigit>", "0"],
    "<utf_characters>": ["á", "ç", "É", "é"],
    "<character>": ["<alnum>"
        , "\"", "!", "#", "$", "%", "&", "\\x27"
        , "\\(", "\\)", "\\*", "+", ",", "-", ".", "/"
        , ":", ";", "<", "=", ">", "?", "@", "["
        , "\\\\", "]", "^", "_", "`", "{", "\\,", "}", "~"
        , " ", "\\t", "\\n", "\\r", "\\x0b", "\\x0c"
        , "<utf_characters>"],
    "<alpha>": srange(string.ascii_letters),
    "<alnum>": ["<alpha>", "<digit>"],
    "<cntrl>": ["\\x0" "<upper_xdigit>", "\\x1" "<upper_xdigit>", "\\x7F"],
    "<graph>": ["\\x2" "<special_digit_1>", "\\x3" "<upper_xdigit>", "\\x4" "<upper_xdigit>", "\\x5" "<upper_xdigit>",
                "\\x6" "<upper_xdigit>", "\\x7" "<special_digit_2>"],
    "<space>": [" ", "\\t", "\\r", "\\n", "\\v", "\\f"],
    "<int_>": ["<nonzerodigit>" "<digits>", "-" "<digit>" "<digits>", "<digit>", "-" "<digit>"],
    "<digits>": ["<digit>" "<digits>", "<digit>"],
    "<nonzerodigit>": ["1", "2", "3", "4", "5", "6", "7", "8", "9"],
    "<upper_xdigit>": ["A", "B", "C", "D", "E", "F", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
    "<special_digit_1>": ["A", "B", "C", "D", "E", "F", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
    "<special_digit_2>": ["A", "B", "C", "D", "E", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
    "<print>": ["\\x2" "<upper_xdigit>", "\\x3" "<upper_xdigit>", "\\x4" "<upper_xdigit>", "\\x5" "<upper_xdigit>",
                "\\x6" "<upper_xdigit>", "\\x7" "<special_digit_2>"],

}

REDUCED_GREP_GRAMMAR: Grammar = {
    "<start>": [
        "<pattern>"
    ],
    "<pattern>": [
        "'<regex>"
    ],
    "<regex>": [
        "",
        "<expression>"
    ],
    "<expression>": [
        "<bracket_expr>",
        "",
        "<expression>|<expression>",
    ],
    "<bracket_expr>": [
        "[<bracket_char_>]",
    ],
    "<bracket_char_>": [
        "<bracket_char>",
        "<bracket_char><bracket_char_>"
    ],
    "<bracket_char>": [
        "0"
    ],
}
