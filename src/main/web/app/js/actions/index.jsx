import fetch from 'isomorphic-fetch'

export const RECEIVE_FUNCTION_VALIDITY = 'RECEIVE_FUNCTION_VALIDITY'
export const RECEIVE_INDUCTION_SCHEMA = 'RECEIVE_INDUCTION_SCHEMA'
export const SAVE_BASE_INITIAL_TERM = 'SAVE_BASE_INITIAL_TERM'
export const RECEIVE_BASE_PROOF_STEP_VALIDITY = 'RECEIVE_BASE_PROOF_STEP_VALIDITY'
export const TOGGLE_PROOF_MODE = 'TOGGLE_PROOF_MODE'
export const RECEIVE_TO_SHOW_VALIDATION = 'RECEIVE_TO_SHOW_VALIDATION'
export const ADD_PROOF_NODE = 'ADD_PROOF_NODE'
export const SAVE_GIVEN_INDEX = 'SAVE_GIVEN_INDEX'
export const COMPLETE_GIVEN_ENTRY = 'COMPLETE_GIVEN_ENTRY'
export const SET_PROOF_STEP_TYPE = 'SET_PROOF_STEP_TYPE'
export const SELECT_LINE = 'SELECT_LINE'
export const DESELECT_LINE = 'DESELECT_LINE'

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
          dispatch(addGivenProofNode(formula))
          const givenIndex = getState().proof.length - 1
          dispatch(saveGivenIndex(givenIndex))
          return Promise.resolve()
        } else {
          return Promise.reject()
        }
      })
  }
}

export const addGivenProofNode = (formula) => {
  return (dispatch, getState) => {

    const lineNo = getState().proof.length + 1
    const proofNode = {
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

export const setProofStepType = (type) => (
  {
    type: SET_PROOF_STEP_TYPE,
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

