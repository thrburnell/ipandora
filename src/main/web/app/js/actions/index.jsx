import fetch from 'isomorphic-fetch'
import { ASSERT_JUSTIFICATION_TYPE, EQUALITY_JUSTIFICATION } from '../constants'

export const RECEIVE_FUNCTION_VALIDITY = 'RECEIVE_FUNCTION_VALIDITY'
export const RECEIVE_INDUCTION_SCHEMA = 'RECEIVE_INDUCTION_SCHEMA'
export const SAVE_BASE_INITIAL_TERM = 'SAVE_BASE_INITIAL_TERM'
export const RECEIVE_BASE_PROOF_STEP_VALIDITY = 'RECEIVE_BASE_PROOF_STEP_VALIDITY'
export const TOGGLE_PROOF_MODE = 'TOGGLE_PROOF_MODE'
export const RECEIVE_TO_SHOW_VALIDATION = 'RECEIVE_TO_SHOW_VALIDATION'
export const ADD_PROOF_NODE = 'ADD_PROOF_NODE'
export const ADD_BASE_CASE_PROOF_NODE = 'ADD_BASE_CASE_PROOF_NODE'
export const ADD_INDUCTIVE_CASE_PROOF_NODE = 'ADD_INDUCTIVE_CASE_PROOF_NODE'
export const SAVE_GIVEN_INDEX = 'SAVE_GIVEN_INDEX'
export const COMPLETE_GIVEN_ENTRY = 'COMPLETE_GIVEN_ENTRY'
export const COMPLETE_TO_SHOW_ENTRY = 'COMPLETE_TO_SHOW_ENTRY'
export const SET_PROOF_STEP_TYPE = 'SET_PROOF_STEP_TYPE'
export const SELECT_LINE = 'SELECT_LINE'
export const DESELECT_LINE = 'DESELECT_LINE'
export const MAKE_ASSERTION = 'MAKE_ASSERTION'
export const CLOSE_PROOF_STEP = 'CLOSE_PROOF_STEP'
export const CLOSE_BASE_CASE_PROOF_STEP = 'CLOSE_BASE_CASE_PROOF_STEP'
export const CLOSE_INDUCTIVE_CASE_PROOF_STEP = 'CLOSE_INDUCTIVE_CASE_PROOF_STEP'
export const SAVE_ARBITRARY = 'SAVE_ARBITRARY'
export const SET_PROOF_COMPLETE = 'SET_PROOF_COMPLETE'
export const SET_BASE_CASE_PROOF_COMPLETE = 'SET_BASE_CASE_PROOF_COMPLETE'
export const SET_BASE_CASE_PROOF_COMPLETE_ERROR = 'SET_BASE_CASE_PROOF_COMPLETE_ERROR'
export const SET_BASE_CASE_PROOF_STEP_TYPE = 'SET_BASE_CASE_PROOF_STEP_TYPE'
export const SET_INDUCTIVE_CASE_PROOF_COMPLETE = 'SET_INDUCTIVE_CASE_PROOF_COMPLETE'
export const SET_INDUCTIVE_CASE_PROOF_COMPLETE_ERROR = 'SET_INDUCTIVE_CASE_PROOF_COMPLETE_ERROR'
export const SET_INDUCTIVE_CASE_PROOF_STEP_TYPE = 'SET_INDUCTIVE_CASE_PROOF_STEP_TYPE'

export const validateFunction = (fn) => {
  return (dispatch, getState) => {

    const request = new Request('/api/predicate/function', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify({
        function: fn
      })
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveFunctionValidity(fn, json.prototype, json.valid))
      })
      .catch(err => console.log(err))
  }
}

export const receiveFunctionValidity = (fn, prototype, valid) => (
  {
    type: RECEIVE_FUNCTION_VALIDITY,
    fn,
    prototype,
    valid
  }
)

export const getInductionSchema = (formula, variable) => {
  return (dispatch, getState) => {
  
    const request = new Request('/api/predicate/induction', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify({
        goal: formula,
        variable
      })
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveInductionSchema(json.goal, json.baseCase, json.inductiveCase))
        dispatch(receiveToShowValidation(formula, true))
        dispatch(completeToShowEntry())
      })
      .catch(err => console.log(err))
  }
}

export const receiveInductionSchema = (toShow, baseCase, inductiveCase) => (
  {
    type: RECEIVE_INDUCTION_SCHEMA,
    toShow,
    baseCase,
    inductiveCase
  }
)

export const saveBaseInitialTerm = (term) => (
  {
    type: SAVE_BASE_INITIAL_TERM,
    term
  }
)

export const makeBaseProofStep = (term, justification) => {
  return (dispatch, getState) => {

    const steps = getState().baseCase.steps
    const latest = steps[steps.length-1].term
    
    const body = {
      method: justification,
      goal: term,
      from: latest
    }

    if (justification == 'FUNCTION_DEFINITION') {
      body.function = getState().fn.definition
      body.functions = getState().prototypes
    }

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify(body)
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveBaseProofStepValidity(term, justification, json.valid))
      })
      .catch(err => console.log(err))
  }
}

export const receiveBaseProofStepValidity = (term, justification, valid) => (
  {
    type: RECEIVE_BASE_PROOF_STEP_VALIDITY,
    term,
    justification,
    valid
  }
)






export const toggleProofMode = () => (
  {
    type: TOGGLE_PROOF_MODE
  }
)

export const validateToShow = (formula) => {
  return (dispatch, getState) => {
    
    const request = new Request("/api/predicate/formula", {
      headers: new Headers({
        "Content-Type": "application/json"
      }),
      method: "post",
      body: JSON.stringify({
        formula
      })
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveToShowValidation(formula, json.valid))
        dispatch(completeToShowEntry())
      })
      .catch(err => console.log(err))
  }
}

export const receiveToShowValidation = (formula, valid) => (
  {
    type: RECEIVE_TO_SHOW_VALIDATION,
    formula,
    valid
  }
)

const makeRequest = (url, body) => {
  const request = new Request(url, {
    headers: new Headers({
      "Content-Type": "application/json"
    }),
    method: "post",
    body: JSON.stringify(body)
  })

  return fetch(request).then(res => res.json()).catch(err => console.log(err))
}

export const addGiven = (formula) => {
  return (dispatch, getState) => {

    return makeRequest("/api/predicate/formula", { formula })
      .then(json => {
        
        if (json.valid) {
          const givenIndex = getState().proof.length
          const lineNo = getState().proof.length + 1
          dispatch(addGivenProofNode(formula, givenIndex, lineNo))
          dispatch(saveGivenIndex(givenIndex))
          return Promise.resolve()
        } else {
          return Promise.reject()
        }
      })
  }
}

export const addGivenProofNode = (formula, id, lineNo) => {
  return (dispatch, getState) => {

    const proofNode = {
      id,
      lineNo,
      body: formula,
      type: "GIVEN",
      valid: true
    }
    
    dispatch(addProofNode(proofNode))
  }
}

export const addProofNode = (node) => (
  {
    type: ADD_PROOF_NODE,
    node
  }
)

export const saveGivenIndex = (index) => (
  {
    type: SAVE_GIVEN_INDEX,
    index
  }
)

export const completeGivenEntry = () => (
  {
    type: COMPLETE_GIVEN_ENTRY
  }
)

export const completeToShowEntry = () => (
  {
    type: COMPLETE_TO_SHOW_ENTRY
  }
)

export const setProofStepType = (type) => (
  {
    type: SET_PROOF_STEP_TYPE,
    proofStepType: type
  }
)

export const setBaseCaseProofStepType = (type) => (
  {
    type: SET_BASE_CASE_PROOF_STEP_TYPE,
    proofStepType: type
  }
)

export const setInductiveCaseProofStepType = (type) => (
  {
    type: SET_INDUCTIVE_CASE_PROOF_STEP_TYPE,
    proofStepType: type
  }
)

export const toggleLine = (index) => {
  return (dispatch, getState) => {

    const selected = getState().selectedLines.indexOf(index) > -1

    if (selected) {
      dispatch(deselectLine(index))
    } else {
      dispatch(selectLine(index))
    }
  }
}

export const selectLine = (index) => (
  {
    type: SELECT_LINE,
    index
  }
)

export const deselectLine = (index) => (
  {
    type: DESELECT_LINE,
    index
  }
)

export const makeAssertion = (formula, justification, area) => {
  switch (justification) {
    case ASSERT_JUSTIFICATION_TYPE.IMPLICATION:
      return makeLogicalImplicationAssertion(formula, area)

    case ASSERT_JUSTIFICATION_TYPE.ASSUMPTION_CLOSURE:
      return makeAssumptionClosureAssertion(formula, area)
  }
}

const makeAssumptionClosureAssertion = (formula, area) => {

  return (dispatch, getState) => {
    const isChild = (child, parent) => {
      if (child == parent) {
        return true
      }

      const nonVal = getState().proof[child].nonValidDependencies || []
      for (const p of nonVal) {
        if (isChild(p, parent)) {
          return true
        }
      }

      return false
    }
    
    const selected = [...getState().selectedLines].sort((a, b) => a - b)

    if (selected.length != 2) {
      return Promise.reject()
    }

    const antecedant = selected[0]
    const consequent = selected[1]
    if (getState().proof[antecedant].type != "ASSUMPTION") {
      return Promise.reject()
    }
    if (!isChild(consequent, antecedant)) {
      return Promise.reject()
    }

    // We have necessary condition for -> Intro
    const impliesFormula = getState().proof[antecedant].body + " -> " + 
      getState().proof[consequent].body

    const body = {
      first: formula,
      second: impliesFormula
    }

    return makeRequest("/api/predicate/equivalent", body)
      .then(json => {
        if (json.equivalent) {
          const id = getState().proof.length
          const lineNo = getState().proof.length + 1

          const node = {
            id,
            lineNo,
            body: formula,
            type: "ASSERTION",
            justification: {
              type: "ASSUMPTION_CLOSURE",
              antecedant,
              consequent
            },
            valid: true
          }

          dispatch(addProofNode(node))
          dispatch(closeProofStep())
          return Promise.resolve()
        } else {
          return Promise.reject()
        }
      })


    return Promise.resolve()
  }
}

const makeLogicalImplicationAssertion = (formula, area) => {
  return (dispatch, getState) => {
    const assumptions = getState().selectedLines
      .filter(i => getState().proof[i].type != "TAKE_ARBITRARY")
      .map(i => getState().proof[i].body)

    const arbs = getState().selectedLines
      .filter(i => getState().proof[i].type == "TAKE_ARBITRARY")
      .map(i => getState().proof[i].element.name)

    if (arbs.length > 1) {
      return Promise.reject()
    }
    
    const body = {
      method: "LOGICAL_IMPLICATION",
      goal: formula,
      assumptions
    }

    if (arbs.length > 0) {
      body.arbitrary = arbs[0]
    }

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify(body)
    })

    return new Promise((resolve, reject) => {

      fetch(request)
        .then(res => res.json())
        .then(json => {
          if (json.valid) {

            const by = getState().selectedLines
            const nonValidDependencies = by.filter(i => 
              getState().proof[i].type != "TAKE_ARBITRARY" && !getState().proof[i].valid
            )

            const id = getState().proof.length
            const lineNo = getState().proof.length + 1
            const node = {
              id,
              lineNo,
              body: formula,
              type: "ASSERTION",
              justification: {
                type: "LOGICAL_IMPLICATION",
                by
              },
              valid: nonValidDependencies.length == 0,
              nonValidDependencies,
            }

            dispatch(addProofNode(node))
            dispatch(closeProofStep())
            resolve()
          } else {
            reject()
          }
        })
        .catch(err => console.log(err))
    })

  }
}

export const makeAssumption = (formula, area) => {
  return (dispatch, getState) => {
    
    return makeRequest("/api/predicate/formula", { formula })
      .then(json => {
        
        if (json.valid) {
          const id = getState().proof.length
          const lineNo = getState().proof.length + 1

          const node = {
            id,
            lineNo,
            body: formula,
            type: "ASSUMPTION",
            valid: false
          }

          dispatch(addProofNode(node))
          dispatch(closeProofStep())
          return Promise.resolve()
        } else {
          return Promise.reject()
        }
      })
  }
}

export const closeProofStep = () => (
  {
    type: CLOSE_PROOF_STEP
  }
)

export const closeBaseCaseProofStep = () => (
  {
    type: CLOSE_BASE_CASE_PROOF_STEP
  }
)

export const closeInductiveCaseProofStep = () => (
  {
    type: CLOSE_INDUCTIVE_CASE_PROOF_STEP
  }
)

export const takeArbitrary = (name, domain, area) => {
  return (dispatch, getState) => {
    
    return new Promise((resolve, reject) => {
      const clash = getState().arbitrary.find(arb => arb.name == name)
      if (clash) {
        reject()
      } else {
        
        const id = getState().proof.length
        const lineNo = getState().proof.length + 1
        const node = {
          id,
          lineNo,
          body: "Take " + name + " from " + domain + " arbitrary",
          type: "TAKE_ARBITRARY",
          element: {
            name: name,
            domain: domain
          }
        }

        dispatch(saveArbitrary(name, domain))
        dispatch(addProofNode(node))
        dispatch(closeProofStep())
        resolve()
      }
    })
  }
}

export const saveArbitrary = (name, domain) => (
  {
    type: SAVE_ARBITRARY,
    name,
    domain
  }
)

export const markProofComplete = () => {
  return (dispatch, getState) => {

    if (!getState().proof[getState().proof.length - 1].valid) {
      return Promise.reject()
    }

    const body = {
      first: getState().toShow.formula,
      second: getState().proof[getState().proof.length - 1].body
    }
    
    return makeRequest("/api/predicate/equivalent", body)
      .then(json => {
        
        if (json.equivalent) {
          dispatch(setProofComplete())
          return Promise.resolve()
        }

        return Promise.reject()
      })
  }
}

export const markBaseCaseProofComplete = () => {
  return (dispatch, getState) => {

    if (getState().baseCaseProof.length < 2) {
      return Promise.reject()
    }

    const body = {
      first: getState().baseCase.toShow[0].split("=")[1],
      second: getState().baseCaseProof[getState().baseCaseProof.length-1].body
    }

    return makeRequest("/api/predicate/equalstructure", body)
      .then(json => {

        if (json.equal) {
          dispatch(setBaseCaseProofComplete())
          return Promise.resolve()
        } else {
          dispatch(setBaseCaseProofCompleteError())
          return Promise.reject()
        }
      })
  }
}

export const markInductiveCaseProofComplete = () => {
  return (dispatch, getState) => {

    if (getState().inductiveCaseProof.length < 2) {
      return Promise.reject()
    }

    const body = {
      first: getState().inductiveCase.toShow[0].split("=")[1],
      second: getState().inductiveCaseProof[getState().inductiveCaseProof.length-1].body
    }

    return makeRequest("/api/predicate/equalstructure", body)
      .then(json => {

        if (json.equal) {
          dispatch(setInductiveCaseProofComplete())
          return Promise.resolve()
        } else {
          dispatch(setInductiveCaseProofCompleteError())
          return Promise.reject()
        }
      })
  }
}

export const setProofComplete = () => (
  {
    type: SET_PROOF_COMPLETE
  }
)

export const setBaseCaseProofComplete = () => (
  {
    type: SET_BASE_CASE_PROOF_COMPLETE
  }
)

export const setBaseCaseProofCompleteError = () => (
  {
    type: SET_BASE_CASE_PROOF_COMPLETE_ERROR
  }
)

export const setInductiveCaseProofComplete = () => (
  {
    type: SET_INDUCTIVE_CASE_PROOF_COMPLETE
  }
)

export const setInductiveCaseProofCompleteError = () => (
  {
    type: SET_INDUCTIVE_CASE_PROOF_COMPLETE_ERROR
  }
)

export const makeBaseCaseEquality = (term, justification) => {
  switch (justification) {
    case EQUALITY_JUSTIFICATION.ARITHMETIC:
      return makeBaseCaseEqualityArithmetic(term)
 
    case EQUALITY_JUSTIFICATION.FUNCTION_DEFINITION:
      return makeBaseCaseEqualityFunctionDefinition(term)
  }
}

const makeBaseCaseEqualityFunctionDefinition = (term) => {
  return (dispatch, getState) => {
    const body = {
      method: "FUNCTION_DEFINITION",
      goal: term,
      from: getState().baseCaseProof[getState().baseCaseProof.length - 1].body,
      function: getState().fn.definition,
      functions: [ getState().fn.prototype ]
    }

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify(body)
    })

    return new Promise((resolve, reject) => {

      fetch(request)
        .then(res => res.json())
        .then(json => {
          if (json.valid) {

            const node = {
              id: getState().baseCaseProof.length,
              body: term,
              type: "FUNCTION_DEFINITION"
            }

            dispatch(addBaseCaseProofNode(node))
            dispatch(closeBaseCaseProofStep())
            resolve()
          } else {
            reject()
          }
        })
        .catch(err => console.log(err))
    })
  }
}

const makeBaseCaseEqualityArithmetic = (term) => {
  return (dispatch, getState) => {

    const body = {
      method: "ARITHMETIC",
      goal: term,
      from: getState().baseCaseProof[getState().baseCaseProof.length - 1].body
    }

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify(body)
    })

    return new Promise((resolve, reject) => {

      fetch(request)
        .then(res => res.json())
        .then(json => {
          if (json.valid) {

            const node = {
              id: getState().baseCaseProof.length,
              body: term,
              type: "ARITHMETIC"
            }

            dispatch(addBaseCaseProofNode(node))
            dispatch(closeBaseCaseProofStep())
            resolve()
          } else {
            reject()
          }
        })
        .catch(err => console.log(err))
    })
  }
}

export const addBaseCaseProofNode = (node) => (
  {
    type: ADD_BASE_CASE_PROOF_NODE,
    node
  }
)

export const makeInductiveCaseEquality = (term, justification) => {
  switch (justification) {
    case EQUALITY_JUSTIFICATION.ARITHMETIC:
      return makeInductiveCaseEqualityArithmetic(term)
 
    case EQUALITY_JUSTIFICATION.FUNCTION_DEFINITION:
      return makeInductiveCaseEqualityFunctionDefinition(term)
  
    case EQUALITY_JUSTIFICATION.INDUCTIVE_HYPOTHESIS:
      return makeInductiveCaseEqualityInductiveHypothesis(term)
  }
}

const makeInductiveCaseEqualityFunctionDefinition = (term) => {
  return (dispatch, getState) => {
    const body = {
      method: "FUNCTION_DEFINITION",
      goal: term,
      from: getState().inductiveCaseProof[getState().inductiveCaseProof.length - 1].body,
      function: getState().fn.definition,
      functions: [ getState().fn.prototype ]
    }

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify(body)
    })

    return new Promise((resolve, reject) => {

      fetch(request)
        .then(res => res.json())
        .then(json => {
          if (json.valid) {

            const node = {
              id: getState().inductiveCaseProof.length,
              body: term,
              type: "FUNCTION_DEFINITION"
            }

            dispatch(addInductiveCaseProofNode(node))
            dispatch(closeInductiveCaseProofStep())
            resolve()
          } else {
            reject()
          }
        })
        .catch(err => console.log(err))
    })
  }
}

const makeInductiveCaseEqualityArithmetic = (term) => {
  return (dispatch, getState) => {

    const body = {
      method: "ARITHMETIC",
      goal: term,
      from: getState().inductiveCaseProof[getState().inductiveCaseProof.length - 1].body
    }

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify(body)
    })

    return new Promise((resolve, reject) => {

      fetch(request)
        .then(res => res.json())
        .then(json => {
          if (json.valid) {

            const node = {
              id: getState().inductiveCaseProof.length,
              body: term,
              type: "ARITHMETIC"
            }

            dispatch(addInductiveCaseProofNode(node))
            dispatch(closeInductiveCaseProofStep())
            resolve()
          } else {
            reject()
          }
        })
        .catch(err => console.log(err))
    })
  }
}

const makeInductiveCaseEqualityInductiveHypothesis = (term) => {
  return (dispatch, getState) => {
    const body = {
      method: "INDUCTIVE_HYPOTHESIS",
      goal: term,
      from: getState().inductiveCaseProof[getState().inductiveCaseProof.length - 1].body,
      inductiveHypothesis: getState().inductiveCase.hypothesis,
      arbitrary: getState().inductiveCase.arbitrary.name,
      functions: [ getState().fn.prototype ]
    }

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify(body)
    })

    return new Promise((resolve, reject) => {

      fetch(request)
        .then(res => res.json())
        .then(json => {
          if (json.valid) {

            const node = {
              id: getState().inductiveCaseProof.length,
              body: term,
              type: "INDUCTIVE_HYPOTHESIS"
            }

            dispatch(addInductiveCaseProofNode(node))
            dispatch(closeInductiveCaseProofStep())
            resolve()
          } else {
            reject()
          }
        })
        .catch(err => console.log(err))
    })
  }
}

export const addInductiveCaseProofNode = (node) => (
  {
    type: ADD_INDUCTIVE_CASE_PROOF_NODE,
    node
  }
)


