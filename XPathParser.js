(function(global, undefined) {
	'use strict';

	var strundef = typeof undefined;
	var whitespace = '[\\x20\\t\\r\\n\\f]';
	var encoding = '(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+';
	var identifier = encoding.replace( 'w', 'w#' );
	var rescape = /"|\\/g;
	var rtrim = new RegExp( '^' + whitespace + '+|' + whitespace + '+$', 'g' );
	var rmatch = new RegExp( '(?:' + whitespace + '*([~+>,]|' + whitespace + ')' + whitespace + '*)?(?:([:.#]?)(' + encoding + '|\\*)|\\[' + whitespace + '*(' + encoding + ')(?:' + whitespace + '*([~^$|*!]?=)' + whitespace + '*(([\'"])((?:\\\\.|[^\\\\])*?)\\7|' + identifier + '))?' + whitespace + '*\\])', 'g' );

	function substitute( str, prop ) {
		return str.replace(/\$\{([^}]+)\}/g, function ( m, p ) {
			return typeof prop[p] !== strundef ? prop[p] + '' : m;
		});
	}

	var XPathParser = {
		AXES: {
			' ': 'descendant::*',
			'>': 'child::*',
			'~': 'following-sibling::*',
			'+': 'following-sibling::*[1]'
		},
		RAXES: {
			' ': 'ancestor::*',
			'>': 'parent::*',
			'~': 'preceding-sibling::*',
			'+': 'preceding-sibling::*[1]'
		},
		ATTRS: {
			'*': '',
			'T': 'local-name()="${0}"',
			'#': '@id and @id="${0}"',
			'N': '@name and @name="${0}"',
			'.': '@class and contains(concat(" ", @class, " "), concat(" ","${0}"," "))',

			'[': '@${0}',
			'=': '@${0}="${1}"',
			'!=': '@${0}!="${1}"',
			'^=': '(@${0} and starts-with(@${0},"${1}"))',
			'$=': function( name, val ) {
				return substitute('(@${0} and substring(@${0},string-length(@${0})-${P})="${1}")', {'0': name, '1': val, P: val.length - 1});
			},
			'*=': '(@${0} and contains(@${0},"${1}"))',
			'|=': 'starts-with(concat(@${0},"-"),"${1}-")',
			'~=': '(@${0} and contains(concat(" ",@${0}," ")," ${1} "))',

			'contains': 'count(descendant-or-self::node()[contains(text(),"${0}")])>0',
			':root': 'not(parent::*)',
			':empty': '(not(*) and not(string-length()))',
			':lang': '@lang="${0}"',
			':link': '0',
			':visited': '0',
			':hover': '0',
			':active': '0',
			':focus': '0',
			':target': '0',
			':enabled': '0',
			':disabled': '0',
			':checked': '0',
			':contains': '0',

			':nth-child': function( a, b ) {
				if ( a === 0 ) {
					return 'position()=' + b;
				} else if ( a === 1 ) {
					return b === 0 ? '' : 'position()>=' + b;
				}
				return '(position()>=' + b + ' and (position()-' + b +
					') mod ' + a + '=0)';
			},
			':nth-last-child': function( a, b ) {
				if ( a === 0 ) {
					return '(last()-position()+1)=' + b;
				} else if ( a === 1 ) {
					return b === 0 ? '' : '(last()-position()+1)>=' + b;
				}
				return '((position()+' + (b - 1) + ')<=last() and ' +
						'(last()-position()-' + (b - 1) + ') mod ' + a + '=0)';
			},
			':nth-of-type': function( a, b ) {
				return XPathParser.ATTRS[':nth-child'](a, b);
			},
			':nth-last-of-type': function( a, b ) {
				return XPathParser.ATTRS[':nth-last-child'](a, b);
			},
			':first-child': 'position()=1',
			':last-child': 'position()=last()',
			':only-child': 'last()=1',
			':first-of-type': 'position()=1',
			':last-of-type': 'position()=last()',
			':only-of-type': 'last()=1',

			':has': function( text ) {
				return 'count(' + XPathParser.parse( text, 'self::*/' ) + ')>0';
			},
			':not': function( group ) {
				var paths = [], i = -1, token;

				while ( (token = group[++i]) ) {
					paths.push( XPathParser._raxes(token) );
				}

				return paths.join( ' and ' );
			}
		},
		_match: function( queue ) {
			var i = -1,
				arr = [],
				unit, t, type;

			while ( (unit = queue[++i]) ) {
				if ( !unit._skip) {
					type = unit._type;
					if ( (t = this.ATTRS[type]) ) {
						if ( type !== 'T' || unit[0] !== '*' ) {
							t = t.indexOf ? substitute(t, unit) : t(unit[0], unit[1]);
							arr.push( t );
						}
					} else {
						arr.push( '0' );
					}
				} else {
					delete unit._skip;
				}
			}

			return arr.length ? arr.join(' and ') : '';
		},
		_axis: function( queue, prefix, rev ) {
			var union = queue._union || ' ',
				i = -1,
				axis = '',
				token, tag, type, nthType;

			if ( union ) {
				axis =  (rev ? this.RAXES : this.AXES)[union];
			}

			while ( (token = queue[++i]) ) {
				type = token._type;
				if ( type === 'T' ) {
					if ( token[0] !== '*' ) {
						tag = token;
					}
				} else if ( /^(nth|nth-last)-of-type$/.test(type) ) {
					nthType = true;
				}
			}

			if ( tag ) {
				if ( nthType ) {
					tag._skip = true;
					axis = axis.replace( '*', tag[0] );
				}
			}

			return prefix ? prefix + axis : axis;
		},
		_axes: function( token, prefix ) {
			var path = '',
				i = -1,
				j = token.length - 1,
				path = '',
				queue, attr;

			while ( (queue = token[++i]) ) {
				path += this._axis( queue, i === 0 && prefix );
				attr = this._match( queue );
				path += attr ? '[' + attr + ']' : '';
				if ( i < j ) {
					path += '/';
				}
			}

			return path;
		},
		_raxes: function( token ) {
			var prefix = '',
				suffix = '',
				i = token.length,
				skip = false,
				queue, axis, attr;

			if ( i === 0 ) {
				return 'not(' + this._match(token[0]) + ')';
			}

			while ( i-- ) {
				queue = token[i];
				axis = this._axis( queue, false, true );
				attr = this._match( queue );

				if ( !skip ) {
					prefix = attr ? attr + ' and ' : '';
					skip = true;
				} else {
					suffix += axis + (attr ? '[' + attr + ']' : '');
					if ( i > 0 ) {
						suffix += '/';
					}
				}
			}

			return 'not(' + prefix + suffix + ')';
		},
		parse: function( selector, prefix ) {
			var group = parse( selector ),
				paths = [], i = -1, token;

			while ( (token = group[++i]) ) {
				paths.push( this._axes(token, prefix) );
			}

			return paths.join('|');
		}
	};

	var parse = function() {
		var text, index, last;

		function match( regex ) {
			var matched = (regex.lastIndex = index, regex.exec(text));
			return matched && matched.index === index ?
				(index = regex.lastIndex, matched) : null;
		}

		function error() {
			throw [ 'INVALID_SELECTOR', text, index ];
		}

	    function parse() {
	        var queue = [],
	        	chain = [ queue ],
	        	group = [ chain ],
	        	unit, matched, pos;

			while ( (matched = match( rmatch )) ) {
				// Comma/Combinators
				if ( matched[1] ) {
					if ( matched[1] === ',' ) {
						chain._text = text.slice( last, (last = matched.index + 1) );
						group.push( chain = [] );
					}
					if ( queue.length ) {
						chain.push( queue = [] );
					}
					if ( matched[1] !== ',' ) {
						queue._union = matched[1];
					}
				}

				unit = [ (matched[4] || matched[3]).replace(rescape, '\\$&') ];
				if ( matched[6] ) {
					pos = matched[6].charAt(0);
					pos = (pos === '\'' || pos === '"') ? matched[6].slice( 1, -1 ) : matched[6];
					unit.push( pos.replace(/"|\\/g, '\\$&') );
				}
				unit._type = matched[5] || (matched[4] ? '[' : matched[2] || 'T');
				if ( unit[0] === '*' && unit._type !== 'T' ) {
					error();
				}
				if ( (matched[2] == ':') ) {
					unit._type = ':' + matched[3];
					if ( text.charAt(index) === '(' ) {
						index++;
						if ( matched[3] === 'not' || matched[3] === 'has' ) {
							pos = index;
							// Recursively
							unit[0] = parse();
							unit[1] = text.slice( pos, index );
							// Found a closing parentheses
							if ( text.charAt(index) === ')' ) {
								index++;
							} else {
								error();
							}
						} else {
							pos = text.indexOf( ')', index );
							if ( pos !== -1 ) {
								unit[0] = text.slice( index, pos ).replace( rtrim, '' );
								index = pos + 1;
							} else {
								error();
							}

							if ( matched[3].indexOf('nth') === 0 ) {
								pos = unit[0];
								pos = (pos === 'even' ? '2n' : pos === 'odd' ? '2n+1' : (pos.indexOf('n') === -1 ? '0n': '') + pos.replace(/\s*/g, '')).split('n');
								unit[0] = !pos[0] ? 1 : +(pos[0]) | 0;
								unit[1] = +(pos[1]) | 0;
							}
						}
					}
				}
				queue.push( unit );
			}
			chain._text = text.slice( last );
			return group;
		}

		return function( selector ) {
			text = selector.replace( rtrim, '' );
			index = last = 0;
			selector = parse();
			match( /\s*/g );
			last = 0;
			return index < text.length ? error() : selector;
		};
	}();

	// EXPOSE API

	if ( typeof define === 'function' && (define.amd || define.cmd) ) {
		define(function() { return XPathParser; });
	} else {
		global.XPathParser = XPathParser;
	}

})(this);