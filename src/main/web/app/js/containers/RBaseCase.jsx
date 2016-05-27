import { connect } from 'react-redux'
import BaseCase from '../components/BaseCase'

const mapStateToProps = (state) => (
  {
    ...state.baseCase,
    active: state.toShow.valid
  }
)

const mapDispatchToProps = () => ({})

const RBaseCase = connect(
  mapStateToProps,
  mapDispatchToProps
)(BaseCase)

export default RBaseCase

